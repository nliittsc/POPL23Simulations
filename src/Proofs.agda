open import Data.Fin as F hiding (_≺_; _≥_) renaming (_≤_ to _≤ᶠ_)
open import Data.Fin.Properties as F
open import Data.Empty
open import Data.List as L hiding (zipWith)
open import Data.List.Membership.Propositional
open import Data.List.Relation.Binary.Permutation.Propositional
open import Data.List.Relation.Unary.All as All hiding (updateAt; zipWith)
open import Data.Maybe hiding (zipWith)
open import Data.Nat as ℕ
open import Data.Product
open import Data.Sum
open import Data.Unit hiding (_≤_)
open import Data.Vec as V hiding (updateAt; zipWith; _++_; [_])
open import Data.Vec.Functional hiding (_++_; _∷_) renaming ([] to ∅)
open import Data.Vec.Functional.Properties
open import Data.Vec.Functional.Relation.Binary.Pointwise 
open import Data.Vec.Functional.Relation.Binary.Pointwise.Properties renaming (refl to pw-refl; sym to pw-sym; trans to pw-trans)
open import Function
open import Relation.Binary.PropositionalEquality renaming ([_] to ⟨_⟩)
open import Relation.Nullary
open import Relation.Nullary.Product
open import Relation.Nullary.Implication
open import Relation.Nullary.Negation

module Proofs where


data multi {X : Set} (R : X → X → Set) : X → X → Set where
  mrefl : ∀{x} → multi R x x
  miter : ∀{x y z} → multi R x y → R y z → multi R x z


postulate
  num-site : ℕ
  MsgVal : Set


Pid = Fin num-site

Matrix : Set → ℕ → ℕ → Set
Matrix A m n = Vector (Vector A n) m

SqMatrix : Set → ℕ → Set
SqMatrix A n = Matrix A n n

{- Machinery for our server/process -}
MState = SqMatrix ℕ num-site

-- Map updates
infixl 10 _[_←_]
_[_←_] : ∀{A : Set} {n} → Vector A n → Fin n → A → Vector A n
v [ i ← x ] = updateAt i (λ _ → x) v


infixl 10 _[_،_←_]
-- For assigning to the row-col in a matrix
_[_،_←_] : ∀{A : Set} {n m} → Matrix A m n → Fin m → Fin n → A → Matrix A m n
x [ i ، j ← e ] =
  let row  = x i
      row′ = row [ j ← e ]
  in x [ i ← row′ ]

-- the deliverability condition
deliverable : Pid → MState → Pid → MState → Set
deliverable i M j Mⱼ = (∀ k → k ≢ i → M k j ≤ Mⱼ k j) × (M i j ≡ ℕ.suc (Mⱼ i j))

deliverable? : (i j : Pid) (M Mⱼ : MState) → Dec (deliverable i M j Mⱼ)
deliverable? i j M Mⱼ = F.all? (λ x → ¬? (x F.≟ i) →-dec (M x j) ℕ.≤? (Mⱼ x j)) ×-dec (M i j ℕ.≟ suc (Mⱼ i j))

-- The initial local state
M₀ : MState
M₀ = (λ i j → 0)

tick : Pid → Pid → MState → MState
tick i j M = M [ i ، j ← ℕ.suc (M i j) ]

-- Merging two vectors, pointwise. A join operation
infixl 12 _⋄_
_⋄_ : ∀{n} → Vector ℕ n → Vector ℕ n → Vector ℕ n
u ⋄ v = zipWith _⊔_ u v

-- Join two matrices
infixl 12 _⊔ₘ_
_⊔ₘ_ : ∀{n} → SqMatrix ℕ n → SqMatrix ℕ n → SqMatrix ℕ n
x ⊔ₘ y = zipWith (_⋄_) x y


-- Commands to be executed
data Com : Set where
  send : Pid → MsgVal → Com


data Control : Set where
  waiting-on : Pid → Control
  ok : Control


data Ack : Set where
  ! : Ack  -- an positive acknowledgement
  ¿ : Ack  -- a negative acknowledgement

Msgᴮ = MsgVal
Msgᴹ = MState × MsgVal

-- we assume decidable equality
postulate
  _≡ᴹ_ : (z₁ z₂ : Msgᴹ) → Dec (z₁ ≡ z₂)
  _≡ₘ_ : (m₁ m₂ : MsgVal) → Dec (m₁ ≡ m₂)

record ProcStateᴮ : Set where
  constructor proc
  field
    outbuf⟨_⟩ : Control × List (Pid × MsgVal)
    recvdᵇ[_] : List (Pid × MsgVal)

open ProcStateᴮ public

record ProcStateᴹ : Set where
  constructor proc
  field
    stateᵐ⟨_⟩ : MState
    recvdᵐ[_] : List (Pid × MState × MsgVal)

open ProcStateᴹ public



-- Definition of process states
Procᴮ = (List Com) × ProcStateᴮ
Procᴹ = (List Com) × ProcStateᴹ

AckChannels = Pid → Pid → Ack
ChannelStatesᴮ = Pid → Pid → List Msgᴮ
ChannelStatesᴹ = Pid → Pid → List Msgᴹ
-- The definition of a system state
Stateᴮ = (Pid → Procᴮ) × ChannelStatesᴮ × AckChannels
Stateᴹ = (Pid → Procᴹ) × ChannelStatesᴹ

infixl 3 _≈ₘ_
-- Defining an equivalence between lists messages
data _≈ₘ_ : List (Pid × Msgᴮ) → List (Pid × Msgᴹ) → Set where
  empty : [] ≈ₘ []
  same-msg : ∀{lᴮ lᴹ i M m} → lᴮ ≈ₘ lᴹ → ((i , m) ∷ lᴮ) ≈ₘ ((i , M , m) ∷ lᴹ)


infixl 3 _≋ₘ_
_≋ₘ_ : Msgᴮ → Msgᴹ → Set
m ≋ₘ (M , m′) = m ≡ m′

-- The initital states for buffer protocol, depending on a map of commands
s₀ᴮ⟨_⟩ : (coms : (Pid → List Com)) → Stateᴮ
s₀ᴮ⟨ coms ⟩ = (λ i → coms i , proc (ok , []) []) , (λ i j → []) , (λ i j → ¿)

-- Initial states for matrix protocol, depending on a map of commands
s₀ᴹ⟨_⟩ : (coms : (Pid → List Com)) → Stateᴹ
s₀ᴹ⟨ coms ⟩ = (λ i → coms i , proc M₀ []) , (λ i → λ j → [])


insert-msg : Control × List (Pid × MsgVal) → Pid → MsgVal → Control × List (Pid × MsgVal)
insert-msg (c , ob) j v = (c , ob L.++ L.[ (j , v) ])


data Eventᴮ : Set where
  send    : Pid → MsgVal → Eventᴮ
  post    : Pid → MsgVal → Eventᴮ
  ack     : Pid → Eventᴮ
  recv    : Pid × MsgVal → Eventᴮ



data Eventᴹ : Set where
  send : Pid → MsgVal → Eventᴹ
  recv : Pid × MState × MsgVal → Eventᴹ


-- Local step machine for process states in buffer protocol
data _⊢_⟼ᴮ[_]⟨_،_⟩ (i : Pid) : Procᴮ → Eventᴮ → Procᴮ → List (Pid × Msgᴮ) → Set where
  send-bp : ∀{coms ob r j m ob′} →
          i ≢ j → ob′ ≡ insert-msg ob j m →
          i ⊢ ((send j m ∷ coms) , proc ob r) ⟼ᴮ[ send j m ]⟨ (coms , proc ob′ r) ، [] ⟩

  post-bp : ∀{coms s j m msgs} →
          i ≢ j →
          outbuf⟨ s ⟩ ≡ (ok , (j , m) ∷ msgs) →
          let s′ = record s {outbuf⟨_⟩ = (waiting-on j , msgs)}
          in i ⊢ (coms , s) ⟼ᴮ[ post j m ]⟨ (coms , s′) ، [ (j , m) ] ⟩

  ack-bp : ∀{coms s j msgs} →
         i ≢ j → outbuf⟨ s ⟩ ≡ (waiting-on j , msgs) →
         let s′ = record s {outbuf⟨_⟩ = (ok , msgs)}
         in i ⊢ (coms , s) ⟼ᴮ[ ack j ]⟨ (coms , s′) ، [] ⟩

  recv-bp : ∀{coms s j m} →
           let s′ = record s {recvdᵇ[_] = recvdᵇ[ s ] ++ [ (j , m) ]}
           in i ⊢ (coms , s) ⟼ᴮ[ recv (j , m) ]⟨ (coms , s′) ، [] ⟩


-- Local step machine for process states in the matrix protocol
data _⊢_⟼ᴹ[_]⟨_،_⟩ (i : Pid) : Procᴹ → Eventᴹ → Procᴹ → List (Pid × Msgᴹ) → Set where

  send-mp : ∀{coms M r j m M′} →
          M′ ≡ tick i j M → i ≢ j →
          i ⊢ (send j m ∷ coms , proc M r) ⟼ᴹ[ send j m ]⟨ (coms , proc M′ r) ، [ (j , M′ , m) ] ⟩

  recv-mp : ∀{coms M r} {j Mⱼ m} {r′ M′} →
          deliverable i M j Mⱼ →
          r′ ≡ r ++ [ (j , Mⱼ , m) ] →
          M′ ≡  M ⊔ₘ Mⱼ →
          i ⊢ (coms , proc M r) ⟼ᴹ[ recv (j , Mⱼ , m) ]⟨ (coms , proc M′ r′) ، [] ⟩

-- Possibly prove that the first message sent in the buffer protocol would be deliverable in the matrix protocol?
          
postulate
  upd-bufferᴮ : Pid → ChannelStatesᴮ → List Msgᴮ → ChannelStatesᴮ
  upd-bufferᴹ : Pid → ChannelStatesᴹ → List Msgᴹ → ChannelStatesᴹ

-- Global system state machine for Buffer protocol
data _⟿ᴮ_ : Stateᴮ → Stateᴮ → Set where
  sys-send-bp : ∀{Π Π′ chan} {i j m coms coms′ sᵢ sᵢ′} →
           Π i ≡ (coms , sᵢ) →
           i ⊢ (coms , sᵢ) ⟼ᴮ[ send j m ]⟨ (coms′ , sᵢ′)  ، [] ⟩ →
           Π′ ≡ Π [ i ← (coms′ , sᵢ′) ] →
           (Π , chan) ⟿ᴮ (Π′ , chan)


  sys-post-bp : ∀{Π Π′ b b′ ac} {i j m coms sᵢ sᵢ′} →
          Π i ≡ (coms , sᵢ) →
          i ⊢ (coms , sᵢ) ⟼ᴮ[ post j m ]⟨ (coms , sᵢ′) ، [ (j , m) ] ⟩ →
          Π′ ≡ Π [ i ← (coms , sᵢ′) ] →
          b′ ≡ b [ i ، j ← (b i j) ++ [ m ] ] →
          (Π , b , ac) ⟿ᴮ (Π′ , b′ , ac)

  sys-ack-bp : ∀{Π Π′ b ac ac′ pᵢ} {i j} →
               ac j i ≡ ! →
               Π′ ≡ Π [ i ← pᵢ ] →
               ac′ ≡ ac [ j ، i ← ¿ ] →  -- receive the acknowledgement
               i ⊢ (Π i) ⟼ᴮ[ ack j ]⟨ pᵢ ، [] ⟩ →
               (Π , b , ac) ⟿ᴮ (Π′ , b , ac′)

  sys-recv-bp : ∀{Π Π′ b b′ ac ac′} {i j coms sᵢ sᵢ′ m } →
           (∀ k → k F.< j → b k i ≡ []) →
           m ∈ b j i →
           i ⊢ (coms , sᵢ) ⟼ᴮ[ recv (j , m) ]⟨ (coms , sᵢ′) ، [] ⟩ →
           Π′ ≡ Π [ i ← (coms , sᵢ′) ] →
           b′ ≡ b [ j ، i ← L.filter (λ x → x ≡ₘ m) (b j i) ] →
           ac′ ≡ ac [ i ، j ← ! ]  →    -- send the acknoweldgement
           (Π , b , ac) ⟿ᴮ (Π′ , b′ , ac′)

-- Global system state machine for matrix protocol
data _⟿ᴹ_ : Stateᴹ → Stateᴹ → Set where
  sys-send-mp : ∀{Π Π′ b b′} {i j m coms coms′ sᵢ sᵢ′} →
              Π i ≡ (coms , sᵢ) →
              i ⊢ (coms , sᵢ) ⟼ᴹ[ send j m ]⟨ (coms′ , sᵢ′) ، [ (j , stateᵐ⟨ sᵢ′ ⟩ , m) ] ⟩ →
              Π′ ≡ Π [ i ← (coms′ , sᵢ′) ] →
              b′ ≡ b [ i ، j ← (b i j) ++ [ (stateᵐ⟨ sᵢ′ ⟩ , m) ] ] →
              (Π , b) ⟿ᴹ (Π′ , b′)

  sys-recv-mp : ∀{Π Π′ b b′} {i j Mⱼ m} {c sᵢ pᵢ} →
                Π i ≡ (c , sᵢ) →
                (∀ k → k F.< j → ∀ Mₖ m → ((Mₖ , m) ∈ b k i) × (¬ (deliverable i stateᵐ⟨ sᵢ ⟩ k Mₖ))) →
                (Mⱼ , m) ∈ b j i →
                i ⊢ (c , sᵢ) ⟼ᴹ[ recv (j , Mⱼ , m) ]⟨ pᵢ ، [] ⟩ →
                Π′ ≡ Π [ i  ← pᵢ ] →
                b′ ≡ b [ j ، i ← (L.filter (λ x → ¬? (x ≡ᴹ (Mⱼ , m))) (b j i)) ] →  -- remove the message
                (Π , b) ⟿ᴹ (Π′ , b′)


-- defining iterated system steps and termination
_⟿ᴮ*_ : Stateᴮ → Stateᴮ → Set
_⟿ᴮ*_ = multi _⟿ᴮ_ 

_⟿ᴹ*_ : Stateᴹ → Stateᴹ → Set
_⟿ᴹ*_ = multi _⟿ᴹ_ 

_⇓ᴮ_ : Stateᴮ → Stateᴮ → Set
s ⇓ᴮ s′ = s ⟿ᴮ s′ × (¬ (∃[ s″ ] s′ ⟿ᴮ s″))

_⇓ᴹ_ : Stateᴹ → Stateᴹ → Set
s ⇓ᴹ s′ = s ⟿ᴹ s′ × (¬ (∃[ s″ ] s′ ⟿ᴹ s″))


infixl 4 _≈_
-- The equivalence relation between received messages
data _≈_ : List (Pid × MsgVal) → List (Pid × MState × MsgVal) → Set where
  base : [] ≈ []
  induct : ∀ {rᵇ rᵐ j v M} → rᵇ ≈ rᵐ →  (j , v) ∷ rᵇ ≈ (j , M , v) ∷ rᵐ


infix 3 _∼_
-- Defining an equivalence between system states
data _∼_ : Stateᴮ → Stateᴹ → Set where
  initial : ∀{coms s₀ᴮ s₀ᴹ} → s₀ᴮ ≡ s₀ᴮ⟨ coms ⟩ → s₀ᴹ ≡ s₀ᴹ⟨ coms ⟩ → s₀ᴮ ∼ s₀ᴹ

module Simulation (coms : (Pid → List Com)) where
  private
    theorem : ∀{Π b ac} → s₀ᴮ⟨ coms ⟩ ⟿ᴮ* (Π , b , ac) →
              Σ[ (Π′ , b′) ∈ Stateᴹ ] (s₀ᴹ⟨ coms ⟩ ⟿ᴹ* (Π′ , b′)) × (∀ i → recvdᵇ[ proj₂ (Π i) ] ≈ₘ recvdᵐ[ proj₂ (Π′ i) ])

    theorem mrefl = s₀ᴹ⟨ coms ⟩ , mrefl , λ i → empty
    theorem (miter p (sys-send-bp x x₁ x₂)) = {!!}
    theorem (miter p (sys-post-bp x x₁ x₂ x₃)) = {!!}
    theorem (miter p (sys-ack-bp x x₁ x₂ x₃)) = {!!}
    theorem (miter p (sys-recv-bp x x₁ x₂ x₃ x₄ x₅)) = {!!}


-- simulating sends
module SendSimulation (coms : (Pid → List Com)) where
  private
    postulate

    -- theorem : ∀{s} → s₀ᴮ⟨ coms ⟩ ⟿ᴮ* s → Σ[ s′ ∈ Stateᴹ ] (s₀ᴹ⟨ coms ⟩ ⟿ᴹ* s′) × (proj₂ s ≈c proj₂ s′)
    -- theorem = ?



unwrapᵇ : List (Pid × MsgVal) → List MsgVal
unwrapᵇ = L.map proj₂

unwrapᵐ : List (Pid × MState × MsgVal) → List MsgVal
unwrapᵐ = L.map (proj₂ ∘ proj₂)

-- for iterating a step function
infixl 3 _*
_* : ∀{X Z : Set} (f : X → Z → X) → (X → List Z → X)
(step *) x [] = x
(step *) x (z ∷ l) = (step *) (step x z) l

obs-equiv-lemma₂ : ∀ {q q′} → q ≈ q′ → unwrapᵇ q ≡ unwrapᵐ q′
obs-equiv-lemma₂ base = refl
obs-equiv-lemma₂ (induct {j = j} {v = v} {M = M} q≈q′) = cong (v ∷_) (obs-equiv-lemma₂ q≈q′)

-- This lemma will help imply theorem2
obs-equiv-lemma₁ : ∀ {S : Set} {s : S} (step : S → MsgVal → S) (p : ProcStateᴮ) (p′ : ProcStateᴹ) →
                   recvdᵇ[ p ] ≈ recvdᵐ[ p′ ] →
                   (step *) s (unwrapᵇ recvdᵇ[ p ]) ≡ (step *) s (unwrapᵐ recvdᵐ[ p′ ])
obs-equiv-lemma₁ {s = s} step p p′ rᵇ≈rᵐ = cong ((step *) s) (obs-equiv-lemma₂ rᵇ≈rᵐ)

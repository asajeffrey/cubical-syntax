{-# OPTIONS --cubical #-}

open import Cubical.Core.Everything using ( _≡_ ; _≃_ ; _,_ )
open import Cubical.Foundations.Everything using ( ua ; transport ; transport⁻ ; cong ; cong₂ ; refl ; _≡⟨_⟩_ ; _∎ ; _∙_ ; isContr ; fiber ; J ; iso ; isoToPath ; transport⁻Transport ; transportTransport⁻)

data Lift (A : Set) : Set where
  zero : Lift(A)
  suc : A → Lift(A)

data Lift[_] {A : Set} (P : A → Set) : Lift(A) → Set where
  zero : Lift[ P ](zero)
  suc : ∀ {a} → P(a) → Lift[ P ](suc(a))

data Exp(Var : Set) : Set where
  var : Var → Exp(Var)
  app : Exp(Var) → Exp(Var) → Exp(Var)
  lam : Exp(Lift(Var)) → Exp(Var)

data Exp[_] {A : Set} (P : A → Set) : Exp(A) → Set where
  var : ∀ {x} → P(x) → Exp[ P ](var x)
  app : ∀ {M N} → Exp[ P ](M) → Exp[ P ](N) → Exp[ P ](app M N) 
  lam : ∀ {M} → Exp[ Lift[ P ] ](M) → Exp[ P ](lam M)

data _⊎_ (A B : Set) : Set where
  inl : A → (A ⊎ B)
  inr : B → (A ⊎ B)

record Σ {A} (P : A → Set) : Set where
  constructor _,_
  field fst : A
  field snd : P(fst)
open Σ

LiftΣ : ∀ {A} {P : A → Set} → Lift(Σ P) ≡ Σ Lift[ P ]
LiftΣ = isoToPath (iso f f⁻¹ round about) where

  f : ∀ {A} {P : A → Set} → Lift(Σ P) → Σ Lift[ P ]
  f zero = (zero , zero)
  f (suc (x , p)) = (suc x , suc p)
  
  f⁻¹ : ∀ {A} {P : A → Set} → Σ Lift[ P ] → Lift(Σ P)
  f⁻¹ (zero , zero) = zero
  f⁻¹ (suc x , suc p) = suc (x , p)

  round : ∀ {A} {P : A → Set} → (b : Σ Lift[ P ]) → f (f⁻¹ b) ≡ b
  round (zero , zero) = refl
  round (suc x , suc p) = refl

  about : ∀ {A} {P : A → Set} → (a : Lift(Σ P)) → f⁻¹ (f a) ≡ a
  about zero = refl
  about (suc x) = refl

ExpΣ : ∀ {A} {P : A → Set} → Exp(Σ P) ≡ Σ Exp[ P ]
ExpΣ = isoToPath (iso (f refl) (f⁻¹ refl) (round refl) (about refl)) where

  varr : ∀ {A} {P : A → Set} → Σ P → Σ Exp[ P ]
  varr (x , p) = (var x , var p)

  appp : ∀ {A} {P : A → Set} → Σ Exp[ P ] → Σ Exp[ P ] → Σ Exp[ P ]
  appp (M , p) (N , q) = (app M N , app p q)

  lamm : ∀ {A} {P : A → Set} → Σ Exp[ Lift[ P ] ] → Σ Exp[ P ]
  lamm (M , p) = (lam M , lam p)
  
  f : ∀ {A B} {P : A → Set} → (B ≡ Σ P) → Exp(B) → Σ Exp[ P ]
  f eq (var xx) = varr (transport eq xx)
  f eq (app MM NN) = appp (f eq (MM)) (f eq (NN))
  f eq (lam MM) = lamm(f (cong Lift eq ∙ LiftΣ) MM)

  f⁻¹ : ∀ {A B} {P : A → Set} → (B ≡ Σ P) → Σ Exp[ P ] → Exp(B)
  f⁻¹ eq (var x , var p) = var (transport⁻ eq (x , p))
  f⁻¹ eq (app M N , app p q) = app (f⁻¹ eq (M , p)) (f⁻¹ eq (N , q))
  f⁻¹ eq (lam M , lam p) = lam (f⁻¹ (cong Lift eq ∙ LiftΣ) (M , p))

  round : ∀ {A B} {P : A → Set} → (eq : B ≡ Σ P) → (b : Σ Exp[ P ]) → f eq (f⁻¹ eq b) ≡ b
  round eq (var x , var p) = cong varr (transportTransport⁻ eq (x , p))
  round eq (app M N , app p q) = cong₂ appp (round eq (M , p)) (round eq (N , q))
  round eq (lam M , lam p) = cong lamm (round (cong Lift eq ∙ LiftΣ) (M , p))

  about : ∀ {A B} {P : A → Set} → (eq : B ≡ Σ P) → (a : Exp(B)) → f⁻¹ eq (f eq a) ≡ a
  about eq (var x) = cong Exp.var (transport⁻Transport eq x)
  about eq (app M N) = cong₂ app (about eq M) (about eq N)
  about eq (lam M) = cong lam (about (cong Lift eq ∙ LiftΣ) M)

funExpΣ : ∀ {V W} {P : W → Set} → (V ≡ Σ P) → Exp(V) → Exp(W)
funExpΣ eq M = fst (transport ExpΣ (transport (cong Exp eq) M))

data IsInl (V W : Set) : (V ⊎ W) → Set where
  inl : ∀ x → IsInl V W (inl(x))

IsInlΣ : ∀ {V W : Set} → V ≡ (Σ (IsInl V W))
IsInlΣ = isoToPath (iso (λ x → (inl x , inl x)) (λ { (inl x , inl .x) → x }) (λ { (inl x , inl .x) → refl }) (λ x → refl))

weakening : ∀ {V W} → Exp(V) → Exp(V ⊎ W)
weakening = funExpΣ IsInlΣ

module Staged.Effects.Compiler where

open import Function
open import Level

open import Data.Empty
open import Data.Unit using (⊤ ; tt)
open import Data.Bool using (Bool ; true ; false ; if_then_else_)
open import Data.Maybe using (Maybe ; just ; nothing ; maybe)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Nat using (ℕ ; suc ; zero ; _≟_ ; _<ᵇ_ ; ∣_-_∣)
open import Data.List
open import Data.List.Categorical

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Staged.Denote
open import Staged.Value.Core

open import Category.Functor
open import Category.Monad

open import Debug.Trace

module _ where

  open Sig
  open RawFunctor ⦃...⦄

  Name = ℕ

  data LamOp₀ (V : Set) : Set where
    `app₀     : LamOp₀ V
    `fetch₀   : Name → LamOp₀ V
    `abs₀     : Name → LamOp₀ V
    `letbind₀ : Name → LamOp₀ V

  LamSig₀ : (V : Set) → Sig
  S₁ (LamSig₀ V) = LamOp₀ V
  P₁ (LamSig₀ V) l = V
  S₂ (LamSig₀ V) `app₀ = Bool
  S₂ (LamSig₀ V) (`fetch₀ x) = ⊥
  S₂ (LamSig₀ V) (`abs₀ x) = ⊤
  S₂ (LamSig₀ V) (`letbind₀ x) = Bool
  P₂ (LamSig₀ V) l = V

  data LamOp (V : Set) : Set where
    `app     : V → List V → LamOp V
    `fetch   : Name → LamOp V
    `abs     : List Name → LamOp V
    `letbind : Name → V → LamOp V
    
  LamSig : (V : Set) → Sig
  S₁ (LamSig V) = LamOp V
  P₁ (LamSig V) _ = V
  S₂ (LamSig V) (`app v vs) = ⊥
  S₂ (LamSig V) (`fetch n) = ⊥
  S₂ (LamSig V) (`abs n) = ⊤
  S₂ (LamSig V) (`letbind n v) = ⊤
  P₂ (LamSig V) _ = V

  NoOp : Sig
  S₁ NoOp = ⊥
  P₁ NoOp = ⊥-elim
  S₂ NoOp = ⊥-elim
  P₂ NoOp {()}

  variable A B V : Set

  elem : ℕ → List ℕ → Bool
  elem n [] = false
  elem n (m ∷ ns) with n ≟ m
  ... | yes _ = true
  ... | no _  = elem n ns

  record Elim (ζ : Sig) : Set₁ where
    field
      elim : {s₁ : S₁ ζ} {B : S₂ ζ s₁ → Set} {C : Set} →
             ((s₂ : S₂ ζ s₁) → L ⊤ → B s₂) →
             ({s₂ : S₂ ζ s₁} → B s₂ → C) →
             C

  open Elim ⦃ ... ⦄

  instance
    NoOp-Elim : Elim NoOp
    Elim.elim NoOp-Elim {s₁ = ()}

  {-# TERMINATING #-}
  hFree : ⦃ RawFunctor L ⦄ →
          ⦃ Elim ζ ⦄ →
          List Name →
          Tree L (LamSig₀ V ⊕ ζ) A →
          List Name
  hFree b (leaf x) = []
  hFree b (node (inj₁ `app₀) l st _) =
    hFree b (st true l) ++ hFree b (st false l)
  hFree b (node (inj₁ (`fetch₀ n)) l st k) =
    if elem n b
    then []
    else n ∷ [] 
  hFree b (node (inj₁ (`abs₀ n)) l st _) =
    hFree (n ∷ b)  (st tt l)
  hFree b (node (inj₁ (`letbind₀ n)) l st _) =
    hFree b (st true l) ++ hFree (n ∷ b) (st false l)
  hFree {L = L} b (node (inj₂ y) l st _) =
    elim {L = L}
         st
         (hFree b)

  record Modular (L : Set → Set) : Set₁ where
    field
      fwd : L A → (A → Tree L ζ (L B)) → Tree L ζ (L B)

  instance
    id-Modular : Modular id
    Modular.fwd id-Modular a k = k a

    Prod-Modular : ∀ {H} → Modular (H ×_)
    Modular.fwd Prod-Modular (h , a) k with (k a)
    ... | leaf x               = leaf (h , proj₂ x)
    ... | node c (_ , l) st k₁ = node c (h , l) st k₁

    Maybe-Modular : Modular Maybe
    Modular.fwd Maybe-Modular nothing k = leaf nothing
    Modular.fwd Maybe-Modular (just a) k = k a

  open Modular ⦃ ... ⦄

  {-# TERMINATING #-}
  hCc : ⦃ Elim ζ ⦄ →
        ⦃ Modular L ⦄ →
        ⦃ RawFunctor L ⦄ →
        Tree L (LamSig₀ V ⊕ ζ) A →
        Tree L (LamSig  V ⊕ ζ) A
  hCc (leaf x) = leaf x
  hCc (node (inj₁ `app₀) l st k) = do
    lv₁ ← hCc (st true l)
    v ← fwd lv₁ (λ v₁ → do
          lv₂ ← hCc (st false (const tt <$> lv₁))
          fwd lv₂ (λ v₂ →
            node (inj₁ (`app v₁ (v₂ ∷ [])))
                 (const tt <$> lv₂)
                 ⊥-elim
                 leaf))
    hCc (k v)
  hCc (node (inj₁ (`fetch₀ n)) l st k) = do
    node (inj₁ (`fetch n)) l
         ⊥-elim
         (hCc ∘ k)
  hCc (node (inj₁ (`abs₀ n)) l st k) = do
    let free = hFree (n ∷ []) (st tt l)
    lv ← node (inj₁ (`abs (free ++ (n ∷ [])))) l (const (hCc ∘ st tt)) leaf
    v  ← fwd lv (λ v →
           case free of λ where
             [] → return lv
             _  → do
               lvs ← foldl (λ t₁ n → do
                 lvs ← t₁
                 fwd lvs (λ vs → do
                   lv' ← node (inj₁ (`fetch n)) (const tt <$> lvs) ⊥-elim leaf
                   fwd lv' (λ v' →
                     return (const (v' ∷ vs) <$> lv')))) (return (const [] <$> lv)) free
               fwd lvs (λ vs → node (inj₁ (`app v vs)) (const tt <$> lvs) ⊥-elim leaf))
    hCc (k v)
  hCc (node (inj₁ (`letbind₀ n)) l st k) = do
    lv ← hCc (st true l)
    v ← fwd lv (λ v →
          node (inj₁ (`letbind n v)) (const tt <$> lv) (const (hCc ∘ st false)) leaf)
    hCc (k v)
  hCc {ζ = ζ} (node (inj₂ y) l st k) =
    node (inj₂ y) l
         (λ s₂ → hCc ∘ st s₂)
         (hCc ∘ k)

  
  instance
    ProdFunctor : ∀ {ℓ} {a} {F : Set a → Set a} {X : Set ℓ} → ⦃ RawFunctor F ⦄ →
                  RawFunctor {a} {a ⊔ ℓ} ((X ×_) ∘ F)
    RawFunctor._<$>_ ProdFunctor f (x , a) = x , (f <$> a)  -- x , f a

  instance
    MaybeFunctor : ∀ {a b} {F} → ⦃ RawFunctor F ⦄ → RawFunctor {a} {b} (Maybe {b} ∘ F)
    (MaybeFunctor {_} RawFunctor.<$> f) nothing = nothing
    (MaybeFunctor {_} RawFunctor.<$> f) (just x) = just (f <$> x)

  FunLabel = ℕ

  Env : Set → Set; Env V = List (Name × V)

  data Closure (V : Set) : Set where
    clos : List Name → FunLabel → Env V → Closure V

  retrieve : List A → FunLabel → Maybe A
  retrieve [] _ = nothing
  retrieve (x ∷ _) 0 = just x
  retrieve (_ ∷ xs) (suc n) = retrieve xs n

  lookupₐ : Env V → Name → Maybe V
  lookupₐ [] _ = nothing
  lookupₐ ((x , v) ∷ nv) y with x ≟ y
  ... | yes _ = just v
  ... | no  _ = lookupₐ nv y

  Resumptions : (Set → Set) → Sig → Set → Set
  Resumptions L ζ V =
    List (L ⊤ → Tree L (LamSig V ⊕ ζ) (L V))

  try : Maybe A → (A → Tree L ζ (Maybe B)) → Tree L ζ (Maybe B)
  try m f = maybe f (leaf nothing) m

  {-# TERMINATING #-}
  hLam' :  ⦃ Closure V ⊂ V ⦄ → ⦃ RawFunctor L ⦄ →
           Env V → Resumptions L ζ V → ℕ →
           Tree L (LamSig V ⊕ ζ) A →
           Tree  (Maybe ∘ (Resumptions L ζ V ×_) ∘ L)
                 ζ (Maybe (Resumptions L ζ V × A))
  hLam' _ _ zero _ = leaf nothing
  hLam' E funs (suc m) (leaf x)  = leaf (just (funs , x))
  hLam' E funs (suc m) (node (inj₁ (`app v₁ vs)) l st k) =
    try (projectᵛ v₁) λ{ (clos ns f E') →
      try (retrieve funs f) (λ r →
        -- curried function application
        if (length vs) <ᵇ (length ns)
        then (do
          let dif = ∣ length ns - length vs ∣
              ns' = drop dif ns
              vs' = drop dif vs
          hLam' E funs m (k (const (injectᵛ $ clos ns' f (zip ns vs ++ E')) <$> l)))
        else 
          hLam' (zip ns vs ++ E') funs m (r l) >>=
            flip try (λ{ (funs' , lv) →
                hLam' E funs' m (k lv) }))}
  hLam' E funs (suc m) (node (inj₁ (`fetch n)) l _ k) = 
    try (lookupₐ E n) (λ v →
      hLam' E funs m (k (const v <$> l)))
  hLam' E funs (suc m) (node (inj₁ (`abs ns)) l st k) =
    hLam'   E (funs ++ [ st tt ]) m
            (k (const (injectᵛ (clos ns (length funs) E)) <$> l))
  hLam' E funs (suc m) (node (inj₁ (`letbind n v)) l st k) =
    hLam' ((n , v) ∷ E) funs m (st tt l) >>=
      flip try λ{ (funs' , lv) → hLam' E funs' m (k lv) }
  hLam' E funs (suc m) (node (inj₂ c) l st k) =
    node      c (just (funs , l))
              (λ r → flip try (λ{ (funs' , l') →
                                  hLam' E funs' m (st r l') }))
              (flip try λ{ (funs' , lr) → hLam' E funs' m (k lr) })

  data Expr : Set where
    nat  : ℕ → Expr
    lam  : Name → Expr → Expr
    app  : Expr → Expr → Expr
    var  : Name → Expr
    let' : Name → Expr → Expr → Expr

  data Val : Set where
    vnat  : ℕ → Val
    vclos : Closure Val → Val

  instance Closure⊂Val : Closure Val ⊂ Val
  _⊂_.injectᵛ Closure⊂Val = vclos
  _⊂_.projectᵛ Closure⊂Val (vnat _) = nothing
  _⊂_.projectᵛ Closure⊂Val (vclos x) = just x

  ⟦_⟧ : Expr → Tree id (LamSig₀ Val ⊕ NoOp) Val
  ⟦ nat n ⟧ = return (vnat n)
  ⟦ lam x e ⟧ = node (inj₁ (`abs₀ x)) tt (λ _ _ → ⟦ e ⟧) leaf
  ⟦ app e e₁ ⟧ = node (inj₁ `app₀) tt (λ{ true _ → ⟦ e ⟧ ; false _ → ⟦ e₁ ⟧}) leaf
  ⟦ var x ⟧ = node (inj₁ (`fetch₀ x)) tt ⊥-elim leaf
  ⟦ let' x e e₁ ⟧ = node (inj₁ (`letbind₀ x)) tt (λ{ true _ → ⟦ e ⟧ ; false _ → ⟦ e₁ ⟧ }) leaf

  operate : Tree id (LamSig₀ Val ⊕ NoOp) Val → ℕ → Maybe Val
  operate x n with hLam' [] [] n (hCc x)
  ... | leaf nothing = nothing
  ... | leaf (just (_ , v)) = just v


  `x `y `z `u `v `w : Name
  `x = 0
  `y = 1
  `z = 2
  `u = 3
  `v = 4
  `w = 5


  example₀ : Expr
  example₀ = let' `x (nat 5) (var `x)

  ut₀ : operate ⟦ example₀ ⟧ 5 ≡ just (vnat 5)
  ut₀ = refl

  example₁ : Expr
  example₁ = app (lam `x (var `x)) (nat 2)

  ut₁ : operate ⟦ example₁ ⟧ 5 ≡ just (vnat 2)
  ut₁ = refl

  example₂ : Expr
  example₂ = let' `x (lam `y (var `y)) (app (var `x) (nat 6))

  ut₂ : operate ⟦ example₂ ⟧ 10 ≡ just (vnat 6)
  ut₂ = refl

  example₃ : Expr
  example₃ = app (let' `x (nat 1) (lam `y (var `x))) (nat 2)

  ut₃ : operate ⟦ example₃ ⟧ 10 ≡ just (vnat 1)
  ut₃ = refl 

  example₄ : Expr
  example₄ = lam `x (lam `y (lam `z (app (var `x) (var `y))))

  ut₄ : operate ⟦ example₄ ⟧ 10 ≡ just (injectᵛ (clos (`x ∷ []) 0 []))
  ut₄ = refl

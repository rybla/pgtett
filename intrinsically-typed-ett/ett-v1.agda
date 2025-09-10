open import Relation.Binary.PropositionalEquality

data Ctx : Set
data Ty : Ctx → Set
data Tm : ∀ Γ → Ty Γ → Set
data Var : ∀ Γ → Ty Γ → Set

data Ctx where
    nil : Ctx
    _◂_ : ∀ (Γ : Ctx) → Ty Γ → Ctx

Ren : Ctx → Ctx → Set
Ren Γ Γ′ = Ty Γ → Ty Γ′

weakenTy : ∀ Γ ξ →
    Ren Γ (Γ ◂ ξ)

{-# TERMINATING #-}
weakenRen : ∀ Γ Γ′ ξ →
    (ren : Ren Γ Γ′) →
    Ren (Γ ◂ ξ) (Γ′ ◂ ren ξ)

substTy : ∀ Γ ξ → Tm Γ ξ → 
    Ty (Γ ◂ ξ) → 
    Ty Γ

data Ty where
    star : ∀ Γ → Ty Γ
    pi : ∀ Γ → (α : Ty Γ) → Ty (Γ ◂ α) → Ty Γ

data Tm where
    var : ∀ Γ α → Var Γ α → Tm Γ α
    lam : ∀ Γ α β → Tm (Γ ◂ α) β → Tm Γ (pi Γ α β)
    app : ∀ Γ α β → Tm Γ (pi Γ α β) → ∀ (a : Tm Γ α) → Tm Γ (substTy Γ α a β)

data Var where
    z : ∀ Γ α → Var (Γ ◂ α) (weakenTy Γ α α)
    s : ∀ Γ α ξ → Var Γ α → Var (Γ ◂ ξ) (weakenTy Γ ξ α)

weakenTy Γ ξ (star .Γ) = star _
weakenTy Γ ξ (pi .Γ α β) = 
    pi _
        (weakenTy _ ξ α)
        (weakenRen _ _ _ (weakenTy _ ξ) β)

weakenRen Γ Γ′ ξ ren (star .(Γ ◂ ξ)) = star _
weakenRen Γ Γ′ ξ ren (pi .(Γ ◂ ξ) α β) =
    pi _
        (weakenRen _ _ _ ren α)
        (weakenRen _ _ _ (weakenRen _ _ ξ ren) β)

substTy Γ ξ x (star .(Γ ◂ ξ)) = star _
substTy Γ ξ x (pi .(Γ ◂ ξ) α β) = 
    pi _ 
        (substTy _ _ x α)
        (weakenRen _ _ _ (substTy _ _ x) β)

{-
pi Γ (substTy Γ ξ x (weakenTy Γ ξ α))
(weakenRen (Γ ◂ ξ) Γ (weakenTy Γ ξ Γα) (substTy Γ ξ x)
 (weakenRen Γ (Γ ◂ ξ) α (weakenTy Γ ξ) β))
≡ pi Γ α β
-}

applyEq : ∀ {ℓ} (A B : Set ℓ) → B ≡ A → A → B
applyEq A B refl x = x

substWeakenTy : ∀ Γ ξ x α → substTy Γ ξ x (weakenTy Γ ξ α) ≡ α
substWeakenTy Γ ξ x (star .Γ) = refl
substWeakenTy Γ ξ x (pi .Γ α β) =
    trans
        {_}
        {_}
        {pi Γ (substTy Γ ξ x (weakenTy Γ ξ α)) (weakenRen (Γ ◂ ξ) Γ (weakenTy Γ ξ α) (substTy Γ ξ x) (weakenRen Γ (Γ ◂ ξ) α (weakenTy Γ ξ) β))}
        {pi Γ (substTy Γ ξ x (weakenTy Γ ξ α)) (applyEq _ _ (cong (λ hole → Ty (Γ ◂ hole)) (substWeakenTy Γ ξ x α)) β)}
        {pi Γ α β}
        (cong (λ hole → pi Γ (substTy Γ ξ x (weakenTy Γ ξ α)) hole) 
            -- weakenRen (Γ ◂ ξ) Γ (weakenTy Γ ξ α) (substTy Γ ξ x) (weakenRen Γ (Γ ◂ ξ) α (weakenTy Γ ξ) β) ≡ 
            -- applyEq (Ty (Γ ◂ α)) (Ty (Γ ◂ substTy Γ ξ x (weakenTy Γ ξ α))) (cong (λ hole → Ty (Γ ◂ hole)) (substWeakenTy Γ ξ x α)) β
            {!  !}
        )
        {!  !} 

-- substVar : ∀ Γ ξ α → (x : Tm Γ ξ) → Var (Γ ◂ ξ) α → Tm Γ (substTy Γ ξ x α)
-- substVar Γ ξ α x (z .Γ .ξ) = {! x  !}
-- substVar Γ ξ α x (s .Γ α₁ .ξ v) = {!   !}

-- substTm : ∀ Γ ξ α → (x : Tm Γ ξ) → Tm (Γ ◂ ξ) α → Tm Γ (substTy Γ ξ x α)
-- substTm Γ ξ α x (var .(Γ ◂ ξ) .α x₁) = {!   !}
-- substTm Γ ξ α x (lam .(Γ ◂ ξ) α₁ β a) = {!   !}
-- substTm Γ ξ α x (app .(Γ ◂ ξ) α₁ β a a₁) = {!   !}
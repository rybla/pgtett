data Ctx : Set
data Ty : Ctx → Set
data Tm : ∀ γ → Ty γ → Set
data Var : ∀ γ → Ty γ → Set

data Ctx where
    nil : Ctx
    _◂_ : ∀ (γ : Ctx) → Ty γ → Ctx

-- weakenTy : ∀ γ ξ → Ty γ → Ty (γ ◂ ξ)
-- weakenTm : ∀ γ α ξ → Tm γ α → Tm (γ ◂ ξ) (weakenTy γ ξ α)
substTy : ∀ γ ξ → Tm γ ξ → Ty (γ ◂ ξ) → Ty γ
substTm : ∀ γ ξ α → (x : Tm γ ξ) → Tm (γ ◂ ξ) α → Tm γ (substTy γ ξ x α)

data Ty where
    star : ∀ γ → Ty γ
    pi : ∀ γ → (α : Ty γ) → Ty (γ ◂ α) → Ty γ
    weakenTy : ∀ γ ξ → Ty γ → Ty (γ ◂ ξ)

data Tm where
    var : ∀ γ α → Var γ α → Tm γ α
    lam : ∀ γ α β → Tm (γ ◂ α) β → Tm γ (pi γ α β)
    app : ∀ γ α β → Tm γ (pi γ α β) → ∀ (a : Tm γ α) → Tm γ (substTy γ α a β)
    weakenTm : ∀ γ α ξ → Tm γ α → Tm (γ ◂ ξ) (weakenTy γ ξ α)

data Var where
    z : ∀ γ α → Var (γ ◂ α) (weakenTy γ α α)
    s : ∀ γ α ξ → Var γ α → Var (γ ◂ ξ) (weakenTy γ ξ α)

-- weakenTy γ ξ (star .γ) = star (γ ◂ ξ)
-- weakenTy γ ξ (pi .γ α β) = pi (γ ◂ ξ) (weakenTy γ ξ α) {!   !}
-- -- (weakenTy ((γ ◂ ξ) ◂ α) {!   !} {!   !})

-- weakenTm = {!   !} 

substTy γ ξ x (star (.γ ◂ .ξ)) = star γ
substTy γ ξ x (pi (.γ ◂ .ξ) α β) = pi γ (substTy γ ξ x α) {!   !}
substTy γ ξ x (weakenTy γ y α) = α

substTm = {!   !}

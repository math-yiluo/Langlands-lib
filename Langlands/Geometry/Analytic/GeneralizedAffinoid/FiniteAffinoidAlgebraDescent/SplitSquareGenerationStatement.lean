import Langlands.Geometry.Analytic.GeneralizedAffinoid.SplitSquareIdealDescent

/-! # Matched generators of finite modules over a split square -/

noncomputable section

universe u v w

namespace Langlands.Analytic.BoundedAlgHom

/-- Cartan-type gluing of generators over a split square: if `M₁` and `M₂` are
finitely generated over the complete algebras `A₁` and `A₂`, and both images
generate the overlap module `M₁₂` over `A₁₂`, then finitely many matching pairs
`(x k, y k)` (equal images in `M₁₂`) generate `M₁` and `M₂` respectively. -/
def SplitSquareModuleGenerationStatement : Prop :=
  ∀ (K : Type u) [NormedField K]
    (A A₁ A₂ A₁₂ : Type v) [NormedCommRing A] [NormedAlgebra K A]
    [NormedCommRing A₁] [NormedAlgebra K A₁] [CompleteSpace A₁]
    [NormedCommRing A₂] [NormedAlgebra K A₂] [CompleteSpace A₂]
    [NormedCommRing A₁₂] [NormedAlgebra K A₁₂]
    (p₁ : BoundedAlgHom K A A₁) (p₂ : BoundedAlgHom K A A₂)
    (r₁ : BoundedAlgHom K A₁ A₁₂) (r₂ : BoundedAlgHom K A₂ A₁₂),
    Nonempty (SplitSquare p₁ p₂ r₁ r₂) →
    ∀ (M₁ M₂ M₁₂ : Type w) [AddCommGroup M₁] [Module A₁ M₁]
      [AddCommGroup M₂] [Module A₂ M₂] [AddCommGroup M₁₂] [Module A₁₂ M₁₂]
      (u₁ : M₁ →+ M₁₂) (u₂ : M₂ →+ M₁₂),
      (∀ (a : A₁) (m : M₁), u₁ (a • m) = r₁ a • u₁ m) →
      (∀ (a : A₂) (m : M₂), u₂ (a • m) = r₂ a • u₂ m) →
      Module.Finite A₁ M₁ → Module.Finite A₂ M₂ →
      Submodule.span A₁₂ (Set.range u₁) = ⊤ →
      Submodule.span A₁₂ (Set.range u₂) = ⊤ →
      ∃ (n : ℕ) (x : Fin n → M₁) (y : Fin n → M₂),
        (∀ k, u₁ (x k) = u₂ (y k)) ∧
          Submodule.span A₁ (Set.range x) = ⊤ ∧
          Submodule.span A₂ (Set.range y) = ⊤

end Langlands.Analytic.BoundedAlgHom

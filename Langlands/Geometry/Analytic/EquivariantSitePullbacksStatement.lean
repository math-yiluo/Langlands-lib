import Langlands.Geometry.Analytic.EquivariantQuasiEtaleSite
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Statement: fibre products in `Qét(X(G))` and `Ét(X(G))` -/

universe u v z

open CategoryTheory

namespace Langlands.Analytic.SaturatedAtlasPresentation

/-- Statement (fibre products in `Qét(X(G))`): every cospan `U₁ → U₃ ← U₂` of `G`-morphisms over
`X` between `G`-spaces quasi-étale over `X` is completed by `G`-morphisms `W → U₁`, `W → U₂`
over `X` from a `G`-space `W` quasi-étale over `X`, such that the underlying square of analytic
spaces is a pullback square in the localized analytic category: `W = U₁ ×_{U₃} U₂` with the
diagonal action. -/
def EquivariantQuasiEtalePullbacksStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (G : Type z) [Group G] [TopologicalSpace G] (X : GSpace.{u, v, v} K G)
    (U₁ U₂ U₃ : EquivariantQuasiEtaleSite X) (f₁ : U₁ ⟶ U₃) (f₂ : U₂ ⟶ U₃),
    ∃ (W : EquivariantQuasiEtaleSite X) (p₁ : W ⟶ U₁) (p₂ : W ⟶ U₂),
      IsPullback (GSpace.forget.map p₁.left) (GSpace.forget.map p₂.left)
        (GSpace.forget.map f₁.left) (GSpace.forget.map f₂.left)

/-- Statement (fibre products in `Ét(X(G))`): every cospan `U₁ → U₃ ← U₂` of `G`-morphisms over
`X` between `G`-spaces étale over `X` is completed by `G`-morphisms `W → U₁`, `W → U₂` over `X`
from a `G`-space `W` étale over `X`, such that the underlying square of analytic spaces is a
pullback square in the localized analytic category: `W = U₁ ×_{U₃} U₂` with the diagonal
action. -/
def EquivariantEtalePullbacksStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (G : Type z) [Group G] [TopologicalSpace G] (X : GSpace.{u, v, v} K G)
    (U₁ U₂ U₃ : EquivariantEtaleSite X) (f₁ : U₁ ⟶ U₃) (f₂ : U₂ ⟶ U₃),
    ∃ (W : EquivariantEtaleSite X) (p₁ : W ⟶ U₁) (p₂ : W ⟶ U₂),
      IsPullback (GSpace.forget.map p₁.left) (GSpace.forget.map p₂.left)
        (GSpace.forget.map f₁.left) (GSpace.forget.map f₂.left)

end Langlands.Analytic.SaturatedAtlasPresentation

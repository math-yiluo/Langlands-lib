import Langlands.Global.AdelicEisensteinConvergenceStatement
import Langlands.Global.AdelicEisensteinConstantTermStatement

/-! # Comparison of regularity for two root presentations of one parabolic -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints

/-- **Regularity does not depend on the root presentation, up to the threshold.** Let
`p₁ : P₁ → G` and `p₂ : P₂ → G` be parabolics of a connected reductive group over a number
field, identified by `e : P₂ → P₁` over `G` (`e ≫ p₁ = p₂`, equal images), with Levi subgroups
`l₁`, `l₂` of the same image, split components `a₁`, `a₂` and root presentations `r₁`, `r₂`,
which may use different maximal split tori and chambers. For every bound `R` there is a bound
`R'` such that every parameter `λ` of `P₁` whose restriction along `e` is `R'`-regular for `r₂`
is `R`-regular for `r₁`. -/
def RootPresentationRegularityComparisonStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G P₁ M₁ P₂ M₂ : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (A₁ A₂ : CommGroupScheme (Spec (CommRingCat.of F)))
    (p₁ : P₁ ⟶ G) (l₁ : M₁ ⟶ P₁) (a₁ : A₁.toGrp ⟶ M₁) (r₁ : ParabolicRootPresentation p₁ l₁ a₁)
    (p₂ : P₂ ⟶ G) (l₂ : M₂ ⟶ P₂) (a₂ : A₂.toGrp ⟶ M₂) (r₂ : ParabolicRootPresentation p₂ l₂ a₂)
    [Mono r₁.data.i.hom.hom.left] [Fintype (relativeWeylGroup r₁.data.i)]
    [Mono (CommGroupScheme.groupHom r₁.data.f).hom.hom.left]
    [Mono r₂.data.i.hom.hom.left] [Fintype (relativeWeylGroup r₂.data.i)]
    [Mono (CommGroupScheme.groupHom r₂.data.f).hom.hom.left]
    (hA₁ : IsSplitTorus A₁.toGrp) (hT₁ : IsSplitTorus r₁.data.T.toGrp)
    (hA₂ : IsSplitTorus A₂.toGrp) (hT₂ : IsSplitTorus r₂.data.T.toGrp),
    IsConnectedReductive G → ∀ e : P₂ ⟶ P₁, e ≫ p₁ = p₂ →
      SubgroupFunctor.range p₁ = SubgroupFunctor.range p₂ →
      SubgroupFunctor.range (l₁ ≫ p₁) = SubgroupFunctor.range (l₂ ≫ p₂) →
      ∀ R : ℝ, ∃ R' : ℝ, ∀ lam : ComplexCharacterParameter F P₁,
        r₂.IsRegularParameter hA₂ hT₂ R' (parameterRestrict e lam) →
          r₁.IsRegularParameter hA₁ hT₁ R lam

end Langlands.Global

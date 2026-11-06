import Langlands.GroupScheme.HomScheme.TorusSubgroupCharts

/-! # Open charts of closed torus subgroups tested on affine schemes -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.TorusSubgroupModuli

variable {S : Scheme.{u}} {G : GroupScheme S}

/-- The conditions of `IsOpenChart` with the injectivity and openness conditions
required only for affine test schemes. -/
structure IsOpenChartOnAffines {U : Over S} {K : GroupScheme U.left}
    (j : K ⟶ (GroupScheme.baseChange U.hom).obj G) : Prop where
  isClosedSubgroup : IsClosedSubgroup j
  isTorus : RelativeTorus.IsTorus K
  smooth : Smooth U.hom
  injective : ∀ (T : Over S), IsAffine T.left →
    ∀ a b : T ⟶ U, evaluate j a = evaluate j b → a = b
  isOpen : ∀ (T : Over S), IsAffine T.left → ∀ (L : GroupScheme T.left)
    (i : L ⟶ (GroupScheme.baseChange T.hom).obj G),
    IsClosedSubgroup i → RelativeTorus.IsTorus L →
    ∃ V : T.left.Opens, ∀ (T' : Over S) (b : T' ⟶ T), IsAffine T'.left →
      ((∃ a : T' ⟶ U, evaluate j a = evaluate i b) ↔ Set.range b.left.base ⊆ V)

/-- Affine tests suffice for open charts of closed torus subgroups. -/
def IsOpenChartOfAffinesStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S) (U : Over S) (K : GroupScheme U.left)
    (j : K ⟶ (GroupScheme.baseChange U.hom).obj G), IsOpenChartOnAffines j → IsOpenChart j

end Langlands.GroupScheme.TorusSubgroupModuli

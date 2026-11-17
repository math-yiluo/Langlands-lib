import Langlands.GroupScheme.HomScheme.MultiplicativeTypeSubgroupCharts
import Langlands.GroupScheme.HomScheme.ChartCoverTransport

/-! # Actual covers by multiplicative-type subgroup charts -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.MultiplicativeTypeSubgroupModuli

/-- The exact all-field-point chart-cover property for one actual group scheme. -/
def HasChartCover {S : Scheme.{u}} (G : GroupScheme S) : Prop :=
  ∃ (I : Type u) (U : I → Over S) (K : ∀ k, GroupScheme (U k).left)
    (j : ∀ k, K k ⟶ (GroupScheme.baseChange (U k).hom).obj G),
    (∀ k, IsOpenChart (j k)) ∧ CoversFieldPoints j

end Langlands.GroupScheme.MultiplicativeTypeSubgroupModuli

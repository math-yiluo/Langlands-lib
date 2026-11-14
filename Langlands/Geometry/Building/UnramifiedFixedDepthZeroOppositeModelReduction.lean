import Langlands.Geometry.Building.UnramifiedFixedDepthZeroOppositeStatement
import Langlands.Geometry.Building.UnramifiedFixedRootModelStatement
import Langlands.BruhatTits.IntegralModels.IntegralOppositeFactorsStatement
import Langlands.GroupScheme.Rational.RelativeRootNegationProof

/-! # Depth-zero opposite factors from actual root models -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable Langlands.BruhatTits.IntegralModels

namespace Langlands.Geometry.Building

/-- Actual root models with exact depth comparisons and the integral
opposite-factor theorem imply the exact restricted depth-zero target. -/
def UnramifiedFixedDepthZeroOppositeModelReductionStatement : Prop :=
  UnramifiedFixedRootModelStatement.{u} →
    IntegralOppositeFactorsStatement.{u} →
      UnramifiedFixedDepthZeroOppositeStatement.{u}

set_option maxHeartbeats 8000000 in
/-- A value-zero point is integral and outside the radical preimage. The
integral opposite-factor theorem then makes both factors integral; the root
comparison for the opposite root yields the required inequalities. -/
theorem unramifiedFixedDepthZeroOpposite_of_rootModels_of_integralOpposite :
    UnramifiedFixedDepthZeroOppositeModelReductionStatement.{u} := by
  intro hmodel hop F _ _ _ _ G hG S iS hiS T iT f hf
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  have := mono_of_isMaximalSplitTorus hiS
  intro hiT
  have : Mono ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left :=
    mono_of_isMaximalSplitTorus hiT
  intro hE D C hDC fixed φ z hz a ha g hg hg1 hzero g' hg' g'' hg'' hm
  obtain ⟨D₀, T₀, Q₀, hT₀, hQ₀, hcomp⟩ :=
    hmodel F G hG S iS hiS T iT f hf hiT hE D C hDC z hz
  change ∀ a ∈ relativeRoots iS, ∀ g ∈ rootGroupPoints iS a,
    (g ∈ D₀.neutral.integralPoints ↔ 0 ≤ φ z a g) ∧
      (g ∈ Q₀.positivePoints ↔ 0 < φ z a g) at hcomp
  have hgint : g ∈ D₀.neutral.integralPoints :=
    (hcomp a ha g hg).1.mpr hzero.symm.le
  have hgnpos : g ∉ Q₀.positivePoints := by
    intro hgpos
    exact (not_lt_of_ge hzero.le) ((hcomp a ha g hg).2.mp hgpos)
  have hints : g' ∈ D₀.neutral.integralPoints ∧ g'' ∈ D₀.neutral.integralPoints :=
    (hop F G hG S iS hiS D₀ T₀ Q₀ hT₀ hQ₀ a ha g hg hg1 hgint
      g' hg' g'' hg'' hm).mpr hgnpos
  have hna : -a ∈ relativeRoots iS := relativeRootNegation F G hG S iS hiS a ha
  exact ⟨(hcomp (-a) hna g' hg').1.mp hints.1,
    (hcomp (-a) hna g'' hg'').1.mp hints.2⟩

end Langlands.Geometry.Building

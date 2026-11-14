import Langlands.Geometry.Building.UnramifiedSimplyConnectedNormalizerAffineWeylStatement
import Langlands.Geometry.Building.IntegerReflectionNormalizerGeneration
import Langlands.Geometry.Building.UnramifiedQuasiSplitReduction
import Langlands.GroupScheme.Rational.HenselianDiscreteQuasiSplitProof
import Langlands.GroupScheme.Rational.QuasiSplitSimplyConnectedRootGenerationStatement

/-! # The maximal-unramified normalizer image from quasi-split root generation -/

noncomputable section

universe u

open Langlands.GroupScheme Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building.MaximalUnramified

/-- Arbitrary-field quasi-split simply connected root generation implies the
full original normalizer-image assertion over the actual inertia fixed field. -/
def SimplyConnectedNormalizerAffineWeylReductionStatement : Prop :=
  QuasiSplitSimplyConnectedRootGenerationStatement.{u} →
    SimplyConnectedNormalizerAffineWeylStatement.{u}

/-- Apply the proved Henselian quasi-splitness theorem to the actual valuation,
then use the full integer-valued normalizer generation reduction. -/
theorem simplyConnectedNormalizerAffineWeyl_of_quasiSplitRootGeneration :
    SimplyConnectedNormalizerAffineWeylReductionStatement.{u} := by
  intro hgen F _ _ _ _ G _ hG C
  have hq : IsQuasiSplit G :=
    henselianDiscreteQuasiSplit (inertiaFixedField F) (valuation F)
      (valuation_surjective F) (valuationSubring_isHenselian F)
      (residueField_isAlgClosed F) G C.isConnectedReductive
  exact C.normalizerAffineEquiv_range_eq_affineWeylGroup_of_rootGenerated_eq_top
    (hgen (inertiaFixedField F) G hG hq C.S C.i C.isMaximalSplitTorus)

end Langlands.Geometry.Building.MaximalUnramified

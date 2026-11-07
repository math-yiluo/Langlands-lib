import Langlands.Automorphic.GroupSchemeConstantTerm
import Langlands.Global.AdelicSubgroupHaarMeasure

/-! # Actual subgroup constant terms on the chosen rational fundamental domain -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj ENNReal

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global AdelicSubgroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom] (U : GroupScheme.SubgroupFunctor G)
  [hclosed : IsClosed (adelicPoints F G U : Set (AdelicGroupPoints F G))]

local instance subgroupLocallyCompactSpace : LocallyCompactSpace (adelicPoints F G U) :=
  hclosed.locallyCompactSpace

local instance quotientBorelSpace : BorelSpace (RationalQuotient F G U) :=
  rationalQuotientBorelSpace F G U

/-- The actual Haar period on the existing chosen rational lattice transversal. -/
def fundamentalDomainConstantTerm (f : ContinuousRationalFunctions F G)
    (g : AdelicGroupPoints F G) : ℂ :=
  ∫ n in LeftCosetSpace.fundamentalDomain (rationalSubgroup F G U)
    (isDiscrete_rationalSubgroup F G U),
    evaluate F G f ((n : AdelicGroupPoints F G) * g) ∂Measure.haar

/-- The intrinsic unnormalized quotient constant term is its actual Haar-domain period. -/
theorem constantTerm_eq_fundamentalDomainIntegral (f : ContinuousRationalFunctions F G)
    (g : AdelicGroupPoints F G) :
    constantTerm F G U (rationalQuotientHaarMeasure F G U) f g =
      fundamentalDomainConstantTerm F G U f g := by
  exact LeftCosetSpace.integral_quotientMeasure (rationalSubgroup F G U) Measure.haar
    (LeftCosetSpace.fundamentalDomain (rationalSubgroup F G U)
      (isDiscrete_rationalSubgroup F G U))
    (constantTermIntegrand F G U f g)
    (continuous_constantTermIntegrand F G U f g).stronglyMeasurable.aestronglyMeasurable

/-- Mass normalization scales the Haar-domain period by the original intrinsic normalizer. -/
theorem normalizedConstantTerm_eq_fundamentalDomainIntegral
    (f : ContinuousRationalFunctions F G) (g : AdelicGroupPoints F G) :
    constantTerm F G U (normalizedRationalQuotientHaarMeasure F G U) f g =
      (quotientMassNormalizer F G U).toReal •
        ∫ n in LeftCosetSpace.fundamentalDomain (rationalSubgroup F G U)
          (isDiscrete_rationalSubgroup F G U),
          evaluate F G f ((n : AdelicGroupPoints F G) * g) ∂Measure.haar := by
  rw [normalizedRationalQuotientHaarMeasure, constantTerm_smul_measure,
    constantTerm_eq_fundamentalDomainIntegral]
  rfl

/-- For finite intrinsic quotient mass, normalized vanishing is exactly Haar-domain vanishing. -/
theorem normalizedConstantTerm_eq_zero_iff_fundamentalDomainIntegral_eq_zero
    [IsFiniteMeasure (rationalQuotientHaarMeasure F G U)]
    (f : ContinuousRationalFunctions F G) (g : AdelicGroupPoints F G) :
    constantTerm F G U (normalizedRationalQuotientHaarMeasure F G U) f g = 0 ↔
      fundamentalDomainConstantTerm F G U f g = 0 := by
  rw [normalizedConstantTerm_eq_fundamentalDomainIntegral]
  change (quotientMassNormalizer F G U).toReal •
    fundamentalDomainConstantTerm F G U f g = 0 ↔ _
  have hnonzero : (quotientMassNormalizer F G U).toReal ≠ 0 := by
    apply ENNReal.toReal_ne_zero.mpr
    exact ⟨ENNReal.inv_ne_zero.mpr (measure_ne_top _ _),
      quotientMassNormalizer_ne_top F G U⟩
  exact smul_eq_zero_iff_right hnonzero

end Langlands.Automorphic.GroupSchemeFunctions

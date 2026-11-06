import Langlands.Automorphic.GroupSchemeParabolicMeasure
import Langlands.Automorphic.GroupSchemeQuotientL2
import Langlands.Global.AdelicSubgroupNormOne
import Langlands.Analysis.Local.CompactQuotientPeriod

/-! # Actual normalized parabolic periods on the positive adelic quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Set
open scoped CategoryTheory.MonObj

namespace Langlands.Global.AdelicSubgroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom] (U : Langlands.GroupScheme.SubgroupFunctor G)
  [hclosed : IsClosed (adelicPoints F G U : Set (AdelicGroupPoints F G))]

local instance : LocallyCompactSpace (adelicPoints F G U) := hclosed.locallyCompactSpace

/-- The existing intrinsic mass-one quotient measure is exactly canonical Borel-domain
normalization of the unscaled actual subgroup Haar measure. -/
theorem normalizedRationalQuotientHaarMeasure_eq_normalizedMeasure :
    normalizedRationalQuotientHaarMeasure F G U =
      LeftCosetSpace.normalizedMeasure (rationalSubgroup F G U) Measure.haar
        (LeftCosetSpace.fundamentalDomain (rationalSubgroup F G U)
          (isDiscrete_rationalSubgroup F G U)) := by
  unfold normalizedRationalQuotientHaarMeasure quotientMassNormalizer
    rationalQuotientHaarMeasure LeftCosetSpace.haarQuotientMeasure
    LeftCosetSpace.discreteQuotientMeasure LeftCosetSpace.normalizedMeasure
  rw [LeftCosetSpace.quotientMeasure_univ]

end Langlands.Global.AdelicSubgroupPoints

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.QuotientIntegration
open Langlands.GroupScheme

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]
  (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)

/-- The actual evaluated radical maps continuously into the actual ambient norm-one group. -/
def properParabolicNormOneInclusion (P : ProperRationalParabolic G) :
    AdelicSubgroupPoints.adelicPoints F G (properRationalParabolicRadicals hPD hG P) →ₜ*
      normOneSubgroup F G :=
  AdelicSubgroupPoints.normOneInclusion F G (properRationalParabolicRadicals hPD hG P)

theorem properParabolicNormOneInclusion_rational_mem (P : ProperRationalParabolic G)
    (n : AdelicSubgroupPoints.rationalSubgroup F G
      (properRationalParabolicRadicals hPD hG P)) :
    properParabolicNormOneInclusion F G hPD hG P n.val ∈ rationalNormOneSubgroup F G :=
  AdelicSubgroupPoints.normOneInclusion_rational_mem F G _ n

/-- The actual constant-term integrand, evaluated directly at a specified positive-quotient
function, with a norm-one ambient translation. -/
def properParabolicPositivePeriodIntegrand (P : ProperRationalParabolic G)
    (φ : PositiveRationalQuotient F G T i → ℂ) (g : normOneSubgroup F G) :
    AdelicSubgroupPoints.RationalQuotient F G (properRationalParabolicRadicals hPD hG P) → ℂ :=
  periodIntegrand (rationalNormOneSubgroup F G)
    (AdelicSubgroupPoints.rationalSubgroup F G (properRationalParabolicRadicals hPD hG P))
    (properParabolicNormOneInclusion F G hPD hG P).toMonoidHom
    (properParabolicNormOneInclusion_rational_mem F G hPD hG P)
    1 (fun _ => rfl) (fun q => φ (normOneToPositiveQuotient F G T i q)) g

@[simp]
theorem properParabolicPositivePeriodIntegrand_mk (P : ProperRationalParabolic G)
    (φ : PositiveRationalQuotient F G T i → ℂ) (g : normOneSubgroup F G)
    (n : AdelicSubgroupPoints.adelicPoints F G (properRationalParabolicRadicals hPD hG P)) :
    properParabolicPositivePeriodIntegrand F G hPD hG T i P φ g
      (LeftCosetSpace.mk (AdelicSubgroupPoints.rationalSubgroup F G
        (properRationalParabolicRadicals hPD hG P)) n) =
      φ (LeftCosetSpace.mk (positiveRationalSubgroup F G T i)
        ((n : AdelicGroupPoints F G) * (g : AdelicGroupPoints F G))) := by
  change (1 : ℂ)⁻¹ * _ = _
  rw [inv_one, one_mul]
  rfl

/-- Absolute convergence for the actual canonical mass-one parabolic quotient measure. -/
def HasConvergentProperParabolicPositivePeriod (P : ProperRationalParabolic G)
    (φ : PositiveRationalQuotient F G T i → ℂ) (g : normOneSubgroup F G) : Prop :=
  Integrable (properParabolicPositivePeriodIntegrand F G hPD hG T i P φ g)
    (properParabolicQuotientMeasure F G hPD hG P)

/-- The actual all-parabolic constant-term period with the existing mass-one measure. -/
def properParabolicPositivePeriod (P : ProperRationalParabolic G)
    (φ : PositiveRationalQuotient F G T i → ℂ) (g : normOneSubgroup F G) : ℂ :=
  ∫ q, properParabolicPositivePeriodIntegrand F G hPD hG T i P φ g q
    ∂properParabolicQuotientMeasure F G hPD hG P

/-- Exact comparison with the existing normalized character-period interface, with trivial
character and the unscaled actual subgroup Haar measure. -/
theorem properParabolicPositivePeriod_eq_normalizedPeriod (P : ProperRationalParabolic G)
    (φ : PositiveRationalQuotient F G T i → ℂ) (g : normOneSubgroup F G) :
    properParabolicPositivePeriod F G hPD hG T i P φ g =
      normalizedQuotientCharacterPeriod (rationalNormOneSubgroup F G)
        (AdelicSubgroupPoints.rationalSubgroup F G (properRationalParabolicRadicals hPD hG P))
        (properParabolicNormOneInclusion F G hPD hG P).toMonoidHom
        (properParabolicNormOneInclusion_rational_mem F G hPD hG P) 1 (fun _ => rfl)
        (AdelicSubgroupPoints.isDiscrete_rationalSubgroup F G _)
        Measure.haar (fun q => φ (normOneToPositiveQuotient F G T i q)) g := by
  unfold properParabolicPositivePeriod properParabolicQuotientMeasure
  rw [AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure_eq_normalizedMeasure]
  rfl

/-- The continuous positive-quotient realization has exactly the published canonical constant
term integrand, with no scalar or representative change. -/
theorem properParabolicPositivePeriodIntegrand_eq_constantTermIntegrand
    (P : ProperRationalParabolic G) (f : C(PositiveRationalQuotient F G T i, ℂ))
    (g : normOneSubgroup F G) :
    properParabolicPositivePeriodIntegrand F G hPD hG T i P f g =
      constantTermIntegrand F G (properRationalParabolicRadicals hPD hG P)
        (positiveQuotientContinuousPullback F G T i f) (g : AdelicGroupPoints F G) := by
  funext q
  induction q using Quotient.inductionOn with
  | _ n => exact properParabolicPositivePeriodIntegrand_mk F G hPD hG T i P f g n

theorem hasConvergentProperParabolicPositivePeriod_of_continuous
    (P : ProperRationalParabolic G) (f : C(PositiveRationalQuotient F G T i, ℂ))
    (g : normOneSubgroup F G) :
    HasConvergentProperParabolicPositivePeriod F G hPD hG T i P f g := by
  unfold HasConvergentProperParabolicPositivePeriod
  rw [properParabolicPositivePeriodIntegrand_eq_constantTermIntegrand]
  exact hasConvergentNormalizedParabolicConstantTerm F G hPD hG P
    (positiveQuotientContinuousPullback F G T i f) g

theorem properParabolicPositivePeriod_eq_constantTerm
    (P : ProperRationalParabolic G) (f : C(PositiveRationalQuotient F G T i, ℂ))
    (g : normOneSubgroup F G) :
    properParabolicPositivePeriod F G hPD hG T i P f g =
      constantTerm F G (properRationalParabolicRadicals hPD hG P)
        (properParabolicQuotientMeasure F G hPD hG P)
        (positiveQuotientContinuousPullback F G T i f) (g : AdelicGroupPoints F G) := by
  unfold properParabolicPositivePeriod constantTerm
  rw [properParabolicPositivePeriodIntegrand_eq_constantTermIntegrand]

/-- Full actual L2 cuspidality: separate AE convergence and AE vanishing for every proper
rational parabolic, rather than the image of a continuous-function space. -/
def fullAEL2CuspidalLocus : Set (Lp ℂ 2 (positiveRationalQuotientHaarMeasure F G T i)) :=
  {φ | ∀ P : ProperRationalParabolic G,
    (∀ᵐ g ∂(Measure.haar : Measure (normOneSubgroup F G)),
      HasConvergentProperParabolicPositivePeriod F G hPD hG T i P φ g) ∧
    properParabolicPositivePeriod F G hPD hG T i P φ =ᵐ[
      (Measure.haar : Measure (normOneSubgroup F G))] 0}

end Langlands.Automorphic.GroupSchemeFunctions

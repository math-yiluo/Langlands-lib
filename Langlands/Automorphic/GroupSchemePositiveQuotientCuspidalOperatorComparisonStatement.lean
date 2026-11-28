import Langlands.Automorphic.GroupSchemeFullAEL2Integrated
import Langlands.Global.AdelicSplitCenterHaar

/-! # Averaging the full cuspidal operator over the positive split centre -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme Langlands.Analysis

section

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]
  (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
  (hi : Function.Injective (characterRestrict i))
  [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I]
  (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
  [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant]

local notation "S" => fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc

/-- Integrate the restriction of the original cuspidal action to the actual norm-one group,
using its fixed Haar measure and the original full cuspidal Hilbert space. -/
def normOneFullAEL2CuspidalIntegratedAction
    (f : normOneSubgroup F G → ℂ) (hf : Integrable f Measure.haar) :
    S →L[ℂ] S := by
  let π := (fullAEL2CuspidalBoundedRightAction F G hPD hG T i hi I e hc).comp
    (normOneSubgroup F G).subtype
  refine integratedIsometricAction Measure.haar π
    (fun n v => norm_fullAEL2CuspidalBoundedRightAction F G hPD hG T i hi I e hc n v)
    (fun v => ?_) f hf
  have : SecondCountableTopologyEither (normOneSubgroup F G) S :=
    secondCountableTopologyEither_of_left _ _
  exact ((fullAEL2CuspidalOrbitMap F G hPD hG T i hi I e hc v).continuous.comp
    continuous_subtype_val).stronglyMeasurable.aestronglyMeasurable

end

/-- The positive-factor average of an integrable ambient weight is integrable. Its
norm-one integrated operator equals the ambient integrated operator on the original
full cuspidal Hilbert space. -/
def GroupSchemePositiveQuotientCuspidalOperatorComparisonStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom]
    (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (hi : Function.Injective (characterRestrict i))
    [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
    [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant]
    (f : AdelicGroupPoints F G → ℂ) (hf : Integrable f Measure.haar),
    let fOne : normOneSubgroup F G → ℂ := fun n =>
      ∫ a, f (positivePointMap F G T i a * n)
        ∂normalizedPositiveHaarMeasure F G T i hi I e hc
    ∃ hfOne : Integrable fOne Measure.haar,
      fullAEL2CuspidalIntegratedAction F G hPD hG T i hi I e hc Measure.haar f hf =
        normOneFullAEL2CuspidalIntegratedAction F G hPD hG T i hi I e hc fOne hfOne

end Langlands.Automorphic.GroupSchemeFunctions

import Langlands.Automorphic.GroupSchemeFullAEL2
import Langlands.Automorphic.GroupSchemeParabolicQuotientL2

/-! # Canonical continuous cuspidal L2 functions in the full AE carrier -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Set
open scoped CategoryTheory.MonObj

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]
  (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)

local notation "Q" => PositiveRationalQuotient F G T i
local notation "μQ" => positiveRationalQuotientHaarMeasure F G T i
local notation "measuresU" => properParabolicQuotientMeasure F G hPD hG

/-- Canonically normalized continuous cuspidality gives the separate AE period conditions. -/
theorem mem_aeParabolicCuspidalFunctionSubmodule_of_continuous
    (f : C(Q, ℂ))
    (hf : f ∈ positiveParabolicCuspidalSubrepresentation F G T i hPD hG measuresU) :
    (f : Q → ℂ) ∈ aeParabolicCuspidalFunctionSubmodule F G hPD hG T i := by
  have hv := (mem_parabolicCuspidalSubrepresentation F G hPD hG measuresU
    (positiveQuotientContinuousPullback F G T i f)).mp hf
  intro P
  constructor
  · filter_upwards with g
    exact hasConvergentProperParabolicPositivePeriod_of_continuous F G hPD hG T i P f g
  · filter_upwards with g
    change properParabolicPositivePeriod F G hPD hG T i P f g = 0
    rw [properParabolicPositivePeriod_eq_constantTerm]
    exact (hv P).2 g

variable (hi : Function.Injective (characterRestrict i))
  [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I]
  (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
  [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant]

local notation "hR" => haarQuotientMeasureRightInvariant F G T i hi I e hc
local notation "ContinuousCuspL2" =>
  PositiveParabolicCuspidalL2Functions F G T i hPD hG measuresU μQ hR

/-- The existing null-class map lands in the original full AE cuspidal locus. -/
theorem positiveParabolicCuspidalL2ToLp_mem_fullAE (f : ContinuousCuspL2) :
    positiveParabolicCuspidalL2ToLp F G T i hPD hG measuresU μQ hR f ∈
      fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc := by
  let := positiveRationalQuotient_borelSpace F G T i hi I e hc
  apply (mem_aeParabolicCuspidalFunctionSubmodule_congr F G hPD hG T i hi I e hc
    (positiveParabolicCuspidalL2ToLp F G T i hPD hG measuresU μQ hR f)
    (f.val : Q → ℂ) (Lp.stronglyMeasurable _) f.val.continuous.stronglyMeasurable
    (coeFn_positiveParabolicCuspidalL2ToLp F G T i hPD hG measuresU μQ hR f)).mpr
  exact mem_aeParabolicCuspidalFunctionSubmodule_of_continuous F G hPD hG T i f.val
    f.property.1

/-- Codomain restriction of the original faithful continuous cusp-L2 intertwiner. -/
def positiveParabolicCuspidalL2ToFullAE :
    (positiveParabolicCuspidalL2RightAction F G T i hPD hG measuresU μQ hR).IntertwiningMap
      (fullAEL2CuspidalRightAction F G hPD hG T i hi I e hc) where
  toLinearMap :=
    (positiveParabolicCuspidalL2ToLp F G T i hPD hG measuresU μQ hR).toLinearMap.codRestrict
      (fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc)
      (positiveParabolicCuspidalL2ToLp_mem_fullAE F G hPD hG T i hi I e hc)
  isIntertwining' a := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    exact Representation.IntertwiningMap.isIntertwining _ _
      (positiveParabolicCuspidalL2ToLp F G T i hPD hG measuresU μQ hR) a f

/-- Forgetting the full-AE subtype recovers exactly the original Lp intertwiner. -/
theorem fullAEL2CuspidalToLp_comp_positiveParabolicCuspidalL2ToFullAE :
    (fullAEL2CuspidalToLp F G hPD hG T i hi I e hc).comp
      (positiveParabolicCuspidalL2ToFullAE F G hPD hG T i hi I e hc) =
      positiveParabolicCuspidalL2ToLp F G T i hPD hG measuresU μQ hR := by
  rfl

/-- Faithfulness uses the full support of the unchanged canonical quotient measure. -/
theorem positiveParabolicCuspidalL2ToFullAE_injective :
    Function.Injective (positiveParabolicCuspidalL2ToFullAE F G hPD hG T i hi I e hc) := by
  intro f g h
  apply haarPositiveParabolicCuspidalL2ToLp_injective F G T i hPD hG measuresU hi I e hc
  exact congrArg Subtype.val h

/-- The existing algebraic continuous cusp image is contained in the full AE subrepresentation. -/
theorem continuousParabolicCuspidalL2Image_le_fullAE :
    continuousParabolicCuspidalL2Image F G T i hPD hG measuresU μQ hR ≤
      fullAEL2CuspidalSubrepresentation F G hPD hG T i hi I e hc := by
  intro φ hφ
  obtain ⟨f, rfl⟩ := hφ
  exact positiveParabolicCuspidalL2ToLp_mem_fullAE F G hPD hG T i hi I e hc f

end Langlands.Automorphic.GroupSchemeFunctions

import Langlands.Automorphic.GroupSchemeParabolicCuspidal
import Langlands.Automorphic.GroupSchemeQuotientL2

/-! # Continuous parabolic vanishing in the actual positive quotient L² -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.GroupScheme
open Langlands.Global.AdelicGroupPoints Langlands.Global.PositiveRealTorus

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
  (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)

variable [∀ P : ProperRationalParabolic G,
  MeasurableSpace (AdelicSubgroupPoints.RationalQuotient F G
    (properRationalParabolicRadicals hPD hG P))]
  (measuresU : ∀ P : ProperRationalParabolic G,
    Measure (AdelicSubgroupPoints.RationalQuotient F G
      (properRationalParabolicRadicals hPD hG P)))

local notation "Q" => PositiveRationalQuotient F G T i

/-- Pull back actual all-parabolic vanishing along the original positive quotient projection. -/
def positiveParabolicCuspidalSubrepresentation :
    Subrepresentation (continuousPositiveQuotientRightAction F G T i) where
  toSubmodule := (parabolicCuspidalSubrepresentation F G hPD hG measuresU).toSubmodule.comap
    (positiveQuotientContinuousPullback F G T i)
  apply_mem_toSubmodule g f hf := by
    change positiveQuotientContinuousPullback F G T i
      (continuousPositiveQuotientRightAction F G T i g f) ∈
        (parabolicCuspidalSubrepresentation F G hPD hG measuresU).toSubmodule
    rw [positiveQuotientContinuousPullback_rightAction]
    exact (parabolicCuspidalSubrepresentation F G hPD hG measuresU).apply_mem_toSubmodule g hf

@[simp]
theorem mem_positiveParabolicCuspidalSubrepresentation (f : C(Q, ℂ)) :
    f ∈ positiveParabolicCuspidalSubrepresentation F G T i hPD hG measuresU ↔
      positiveQuotientContinuousPullback F G T i f ∈
        parabolicCuspidalSubrepresentation F G hPD hG measuresU := Iff.rfl

variable (measureQ : Measure (PositiveRationalQuotient F G T i))
  (hInvariant : QuotientMeasureRightInvariant F G T i measureQ)

/-- Square integrability is imposed explicitly on the actual continuous quotient functions. -/
def positiveParabolicCuspidalL2Subrepresentation :
    Subrepresentation (continuousPositiveQuotientRightAction F G T i) :=
  positiveParabolicCuspidalSubrepresentation F G T i hPD hG measuresU ⊓
    continuousL2Subrepresentation F G T i measureQ hInvariant

abbrev PositiveParabolicCuspidalL2Functions :=
  (positiveParabolicCuspidalL2Subrepresentation F G T i hPD hG measuresU
    measureQ hInvariant).toSubmodule

def positiveParabolicCuspidalL2RightAction :
    Representation ℂ (AdelicGroupPoints F G)
      (PositiveParabolicCuspidalL2Functions F G T i hPD hG measuresU measureQ hInvariant) :=
  (positiveParabolicCuspidalL2Subrepresentation F G T i hPD hG measuresU
    measureQ hInvariant).toRepresentation

theorem mem_positiveParabolicCuspidalL2Subrepresentation (f : C(Q, ℂ)) :
    f ∈ positiveParabolicCuspidalL2Subrepresentation F G T i hPD hG measuresU
        measureQ hInvariant ↔
      (positiveQuotientContinuousPullback F G T i f ∈
        parabolicCuspidalSubrepresentation F G hPD hG measuresU) ∧
      MemLp f 2 measureQ := Iff.rfl

/-- Forgetting vanishing retains the original continuous square-integrable function. -/
def positiveParabolicCuspidalL2ToContinuousL2 :
    PositiveParabolicCuspidalL2Functions F G T i hPD hG measuresU measureQ hInvariant →ₗ[ℂ]
      continuousL2Submodule F G T i measureQ :=
  (positiveParabolicCuspidalL2Subrepresentation F G T i hPD hG measuresU
    measureQ hInvariant).toSubmodule.inclusion (fun _ hf => hf.2)

/-- Passing to the actual L² null class intertwines the unchanged positive right action. -/
def positiveParabolicCuspidalL2ToLp :
    (positiveParabolicCuspidalL2RightAction F G T i hPD hG measuresU measureQ
      hInvariant).IntertwiningMap (quotientL2RightAction F G T i measureQ hInvariant) where
  toLinearMap := (continuousL2ToLp F G T i measureQ).comp
    (positiveParabolicCuspidalL2ToContinuousL2 F G T i hPD hG measuresU measureQ hInvariant)
  isIntertwining' g := by
    apply LinearMap.ext
    intro f
    exact continuousL2ToLp_rightAction F G T i measureQ hInvariant g
      (positiveParabolicCuspidalL2ToContinuousL2 F G T i hPD hG measuresU measureQ hInvariant f)

theorem coeFn_positiveParabolicCuspidalL2ToLp
    (f : PositiveParabolicCuspidalL2Functions F G T i hPD hG measuresU measureQ hInvariant) :
    positiveParabolicCuspidalL2ToLp F G T i hPD hG measuresU measureQ hInvariant f
      =ᵐ[measureQ] (f.val : Q → ℂ) :=
  coeFn_continuousL2ToLp F G T i measureQ
    (positiveParabolicCuspidalL2ToContinuousL2 F G T i hPD hG measuresU measureQ hInvariant f)

theorem positiveParabolicCuspidalL2ToLp_injective [measureQ.IsOpenPosMeasure] :
    Function.Injective
      (positiveParabolicCuspidalL2ToLp F G T i hPD hG measuresU measureQ hInvariant) := by
  intro f g h
  have he := continuousL2ToLp_injective F G T i measureQ h
  apply Subtype.ext
  exact congrArg (fun z : continuousL2Submodule F G T i measureQ => z.val) he

/-- The algebraic image of continuous, square-integrable, all-parabolic-vanishing functions.
No closure or equality with the full almost-everywhere cuspidal subspace is asserted. -/
def continuousParabolicCuspidalL2Image :
    Subrepresentation (quotientL2RightAction F G T i measureQ hInvariant) :=
  (positiveParabolicCuspidalL2ToLp F G T i hPD hG measuresU measureQ hInvariant).range

theorem mem_continuousParabolicCuspidalL2Image (phi : QuotientL2 F G T i measureQ) :
    phi ∈ continuousParabolicCuspidalL2Image F G T i hPD hG measuresU measureQ hInvariant ↔
      ∃ f : PositiveParabolicCuspidalL2Functions F G T i hPD hG measuresU measureQ hInvariant,
        positiveParabolicCuspidalL2ToLp F G T i hPD hG measuresU measureQ hInvariant f = phi :=
  Iff.rfl

section CanonicalMeasure

variable [LocallyOfFiniteType G.X.hom]
  (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)
  (hc : IsCentral i)
  [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant]

include hi I e hc in
/-- Faithfulness holds for the exact existing Haar-normalized positive quotient measure. -/
theorem haarPositiveParabolicCuspidalL2ToLp_injective :
    Function.Injective (positiveParabolicCuspidalL2ToLp F G T i hPD hG measuresU
      (positiveRationalQuotientHaarMeasure F G T i)
      (haarQuotientMeasureRightInvariant F G T i hi I e hc)) := by
  let := haarQuotientMeasure_isOpenPosMeasure F G T i hi I e hc
  exact positiveParabolicCuspidalL2ToLp_injective F G T i hPD hG measuresU _ _

end CanonicalMeasure

end Langlands.Automorphic.GroupSchemeFunctions

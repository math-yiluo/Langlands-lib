import Langlands.Automorphic.GroupSchemeCuspidalForms
import Langlands.Automorphic.GroupSchemeParabolicQuotientL2

/-! # Finite-smooth parabolic-vanishing forms in the actual positive quotient L² -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.GroupScheme
open Langlands.Global.AdelicGroupPoints Langlands.Global.PositiveRealTorus

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]
  (Kinf : Subgroup (InfiniteAdelicGroupPoints F G))
  {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
  (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth)
  (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)
  (hrho : IsClosedSubgroup rho) (hK : Langlands.CompactIwasawa.IsMaximalCompact Kinf)
  (hN : 0 < N)
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)

local notation "Q" => PositiveRationalQuotient F G T i

/-- Bundle the original faithful cusp-form inclusion for the finite adelic action. -/
def adelicCuspidalContinuousIntertwiner :
    (adelicCuspidalFiniteRightAction F G Kinf rho hsmooth hcalc hPD hG hrho hK hN).IntertwiningMap
      (finiteRightAction F G) where
  toLinearMap := adelicCuspidalToContinuous F G Kinf rho hsmooth hcalc hPD hG hrho hK hN
  isIntertwining' _ := by ext; rfl

/-- Actual continuous functions which possess an original cusp-form representative. -/
def adelicCuspidalContinuousImage : Subrepresentation (finiteRightAction F G) :=
  (adelicCuspidalContinuousIntertwiner F G Kinf rho hsmooth hcalc hPD hG hrho hK hN).range

/-- Restrict the existing positive quotient action to the finite factor. -/
def continuousPositiveQuotientFiniteRightAction :
    Representation ℂ (FiniteAdelicGroupPoints F G) C(Q, ℂ) :=
  (continuousPositiveQuotientRightAction F G T i).comp
    (AdelicGroupPoints.ofFinite F G).toMonoidHom

/-- The actual quotient pullback intertwines the same finite positive action. -/
def positiveQuotientFinitePullback :
    (continuousPositiveQuotientFiniteRightAction F G T i).IntertwiningMap
      (finiteRightAction F G) where
  toLinearMap := positiveQuotientContinuousPullback F G T i
  isIntertwining' _ := by ext; rfl

/-- Positive-center descent is an explicit requirement on the original cusp forms. -/
def positiveCuspidalFormSubrepresentation :
    Subrepresentation (continuousPositiveQuotientFiniteRightAction F G T i) where
  toSubmodule := (adelicCuspidalContinuousImage F G Kinf rho hsmooth hcalc hPD hG hrho hK hN).toSubmodule.comap (positiveQuotientContinuousPullback F G T i)
  apply_mem_toSubmodule c f hf := by
    change positiveQuotientContinuousPullback F G T i
      (continuousPositiveQuotientRightAction F G T i (AdelicGroupPoints.ofFinite F G c) f) ∈
        (adelicCuspidalContinuousImage F G Kinf rho hsmooth hcalc hPD hG hrho hK hN).toSubmodule
    rw [positiveQuotientContinuousPullback_rightAction]
    exact (adelicCuspidalContinuousImage F G Kinf rho hsmooth hcalc hPD hG hrho hK hN).apply_mem_toSubmodule c hf

/-- The pullback must equal a genuine actual cusp form at all adelic points. -/
theorem mem_positiveCuspidalFormSubrepresentation (f : C(Q, ℂ)) :
    f ∈ positiveCuspidalFormSubrepresentation F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i ↔
      ∃ phi : AdelicCuspidalForms F G Kinf rho hsmooth hcalc hPD hG hrho hK hN,
        adelicCuspidalToContinuous F G Kinf rho hsmooth hcalc hPD hG hrho hK hN phi =
          positiveQuotientContinuousPullback F G T i f := Iff.rfl

variable (measureQ : Measure (PositiveRationalQuotient F G T i))
  (hInvariant : QuotientMeasureRightInvariant F G T i measureQ)

/-- The existing continuous L² condition, restricted to the actual finite adelic action. -/
def continuousPositiveFiniteL2Subrepresentation :
    Subrepresentation (continuousPositiveQuotientFiniteRightAction F G T i) where
  toSubmodule := continuousL2Submodule F G T i measureQ
  apply_mem_toSubmodule c _f hf :=
    hf.comp_measurePreserving (hInvariant (AdelicGroupPoints.ofFinite F G c))

/-- The actual cusp-form realization requires genuine MemLp2 separately from descent. -/
def positiveCuspidalFormL2Subrepresentation :
    Subrepresentation (continuousPositiveQuotientFiniteRightAction F G T i) :=
  positiveCuspidalFormSubrepresentation F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i ⊓
    continuousPositiveFiniteL2Subrepresentation F G T i measureQ hInvariant

abbrev PositiveCuspidalFormL2Functions :=
  (positiveCuspidalFormL2Subrepresentation F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i
    measureQ hInvariant).toSubmodule

def positiveCuspidalFormL2FiniteRightAction :
    Representation ℂ (FiniteAdelicGroupPoints F G)
      (PositiveCuspidalFormL2Functions F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i
        measureQ hInvariant) :=
  (positiveCuspidalFormL2Subrepresentation F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i
    measureQ hInvariant).toRepresentation

theorem mem_positiveCuspidalFormL2Subrepresentation (f : C(Q, ℂ)) :
    f ∈ positiveCuspidalFormL2Subrepresentation F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i
        measureQ hInvariant ↔
      (∃ phi : AdelicCuspidalForms F G Kinf rho hsmooth hcalc hPD hG hrho hK hN,
        adelicCuspidalToContinuous F G Kinf rho hsmooth hcalc hPD hG hrho hK hN phi =
          positiveQuotientContinuousPullback F G T i f) ∧ MemLp f 2 measureQ := Iff.rfl

/-- Forgetting the form conditions keeps the same original continuous representative. -/
def positiveCuspidalFormL2ToContinuousL2 :
    PositiveCuspidalFormL2Functions F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i
      measureQ hInvariant →ₗ[ℂ] continuousL2Submodule F G T i measureQ :=
  (positiveCuspidalFormL2Subrepresentation F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i
    measureQ hInvariant).toSubmodule.inclusion (fun _ hf => hf.2)

/-- The actual quotient L² representation restricted to finite translation. -/
def quotientL2FiniteRightAction :
    Representation ℂ (FiniteAdelicGroupPoints F G) (QuotientL2 F G T i measureQ) :=
  (quotientL2RightAction F G T i measureQ hInvariant).comp
    (AdelicGroupPoints.ofFinite F G).toMonoidHom

/-- Pass genuine square-integrable continuous cusp forms to their actual null classes. -/
def positiveCuspidalFormL2ToLp :
    (positiveCuspidalFormL2FiniteRightAction F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i
      measureQ hInvariant).IntertwiningMap (quotientL2FiniteRightAction F G T i measureQ hInvariant) where
  toLinearMap := (continuousL2ToLp F G T i measureQ).comp
    (positiveCuspidalFormL2ToContinuousL2 F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i
      measureQ hInvariant)
  isIntertwining' c := by
    apply LinearMap.ext
    intro f
    exact continuousL2ToLp_rightAction F G T i measureQ hInvariant
      (AdelicGroupPoints.ofFinite F G c)
      (positiveCuspidalFormL2ToContinuousL2 F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i
        measureQ hInvariant f)

theorem coeFn_positiveCuspidalFormL2ToLp
    (f : PositiveCuspidalFormL2Functions F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i
      measureQ hInvariant) :
    positiveCuspidalFormL2ToLp F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i measureQ hInvariant f
      =ᵐ[measureQ] (f.val : Q → ℂ) :=
  coeFn_continuousL2ToLp F G T i measureQ
    (positiveCuspidalFormL2ToContinuousL2 F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i
      measureQ hInvariant f)

/-- Full support makes the continuous form realization injective in the actual L² space. -/
theorem positiveCuspidalFormL2ToLp_injective [measureQ.IsOpenPosMeasure] :
    Function.Injective
      (positiveCuspidalFormL2ToLp F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i measureQ hInvariant) := by
  intro f g h
  have he := continuousL2ToLp_injective F G T i measureQ h
  apply Subtype.ext
  exact congrArg (fun z : continuousL2Submodule F G T i measureQ => z.val) he

/-- The algebraic image in actual quotient L² retains the original finite action. -/
def cuspidalFormQuotientL2Image :
    Subrepresentation (quotientL2FiniteRightAction F G T i measureQ hInvariant) :=
  (positiveCuspidalFormL2ToLp F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i
    measureQ hInvariant).range

/-- Compatibility with the published continuous-only parabolic-vanishing L² construction. -/
def positiveCuspidalFormL2ToContinuousParabolic :
    PositiveCuspidalFormL2Functions F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i
      measureQ hInvariant →ₗ[ℂ]
      PositiveParabolicCuspidalL2Functions F G T i hPD hG
        (properParabolicQuotientMeasure F G hPD hG) measureQ hInvariant where
  toFun f := ⟨f.val, by
    refine ⟨?_, f.property.2⟩
    obtain ⟨phi, hphi⟩ := f.property.1
    change positiveQuotientContinuousPullback F G T i f.val ∈
      normalizedParabolicCuspidalSubrepresentation F G hPD hG
    rw [← hphi]
    exact phi.property.2⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

/-- Both realizations have exactly the same continuous representative and actual L² class. -/
theorem positiveCuspidalFormL2ToContinuousParabolic_toLp
    (f : PositiveCuspidalFormL2Functions F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i
      measureQ hInvariant) :
    positiveParabolicCuspidalL2ToLp F G T i hPD hG
        (properParabolicQuotientMeasure F G hPD hG) measureQ hInvariant
        (positiveCuspidalFormL2ToContinuousParabolic F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i
          measureQ hInvariant f) =
      positiveCuspidalFormL2ToLp F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i
        measureQ hInvariant f := rfl

section CanonicalMeasure

variable (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)
  (hc : IsCentral i)
  [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant]

include hi I e hc in
/-- The exact existing Haar quotient measure satisfies the same faithful form realization. -/
theorem haarPositiveCuspidalFormL2ToLp_injective :
    Function.Injective (positiveCuspidalFormL2ToLp F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i
      (positiveRationalQuotientHaarMeasure F G T i)
      (haarQuotientMeasureRightInvariant F G T i hi I e hc)) := by
  let := haarQuotientMeasure_isOpenPosMeasure F G T i hi I e hc
  exact positiveCuspidalFormL2ToLp_injective F G Kinf rho hsmooth hcalc hPD hG hrho hK hN T i _ _

end CanonicalMeasure

end Langlands.Automorphic.GroupSchemeFunctions

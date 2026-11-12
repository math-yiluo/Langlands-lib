import Langlands.Global.NumberFieldSpaceFixedModelWeilHomeomorph
import Langlands.Global.AdelicSpaceWeilRestrictionPoints
import Langlands.Global.NumberFieldSIntegerFinite
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceWeilRestrictionBaseChangeEvaluation
import Langlands.Global.AdelicSpaceStageComparison

/-! # Original generic-fibre comparison of a number-field space Weil model -/

noncomputable section

universe u

open CategoryTheory Topology IsDedekindDomain
open _root_.AlgebraicGeometry
open scoped NumberField TensorProduct Langlands.Global Langlands.Global.NumberFieldSIntegers

namespace Langlands.Global.NumberFieldSpaceWeilGenericFiber

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open NumberFieldSIntegerSpaceWeilTopology (lowerCoefficients upperCoefficients)
open AdelicFunctoriality

set_option backward.isDefEq.respectTransparency false

variable (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] (S : Finset (FinitePlace K))
  (X : AlgebraicSpace (Spec (CommRingCat.of (upperCoefficients K L S))))
  (h : IsAlgebraicSpace _
    ((ringWeilRestriction (lowerCoefficients K S) (upperCoefficients K L S)).obj X.toSheaf))

include h in
/-- The generic Weil sheaf is algebraic by the original fraction-field cartesian square. -/
theorem genericWeilAlgebraic : IsAlgebraicSpace _
    ((ringWeilRestriction K L).obj
      (numberFieldSpaceGenericFiber L (numberFieldExceptionalPreimage (L := L) S) X).toSheaf) :=
  isAlgebraicSpace_ringWeilRestriction_tensor (lowerCoefficients K S) (upperCoefficients K L S)
    K L (numberFieldSIntegersFractionTensorEquiv K L S)
    (fun b => by simp only [numberFieldSIntegersFractionTensorEquiv_tmul, map_one, one_mul]; rfl) X h

/-- The actual original integral Weil model has the expected generic fibre. -/
def genericFiberIso :
    numberFieldSpaceGenericFiber K S
      (ringWeilRestrictionSpace (lowerCoefficients K S) (upperCoefficients K L S) X h) ≅
      ringWeilRestrictionSpace K L
        (numberFieldSpaceGenericFiber L (numberFieldExceptionalPreimage (L := L) S) X)
        (genericWeilAlgebraic K L S X h) :=
  ringWeilRestrictionTensorBaseChangeIso (lowerCoefficients K S) (upperCoefficients K L S)
    K L (numberFieldSIntegersFractionTensorEquiv K L S)
    (fun b => by simp only [numberFieldSIntegersFractionTensorEquiv_tmul, map_one, one_mul]; rfl) X h

/-- The full inclusion retains the original field coefficients. -/
theorem adeleInclusion_compatible :
    (adeleInclusion (K := K) (L := L)).comp (algebraMap K (Adeles K)) =
      (algebraMap L (Adeles L)).comp (algebraMap K L) := by
  apply RingHom.ext
  intro a
  exact adeleInclusion_diagonal (K := K) (L := L) a

/-- The generic-fibre canonical adelic map is the original integral counit under both identifications. -/
theorem adelicEvaluation_model
    (p : NumberFieldSpaceAdelePoints K S
      (ringWeilRestrictionSpace (lowerCoefficients K S) (upperCoefficients K L S) X h)) :
    numberFieldSpaceWeilRestrictionPointsEquiv K L
        (numberFieldSpaceGenericFiber L (numberFieldExceptionalPreimage (L := L) S) X)
        (genericWeilAlgebraic K L S X h)
        (numberFieldSpaceSpreadEquiv K S
          (ringWeilRestrictionSpace (lowerCoefficients K S) (upperCoefficients K L S) X h) _
          (genericFiberIso K L S X h) p) =
      numberFieldSpaceGenericFiberEquiv L (numberFieldExceptionalPreimage (L := L) S) X
        (NumberFieldSpaceFixedModelWeilEvaluation.adelicEvaluation K L S X h p) := by
  let algAK : Algebra (lowerCoefficients K S) K :=
    (lowerCoefficients K S).toSubring.subtype.toAlgebra
  let algAR : Algebra (lowerCoefficients K S) (numberFieldAdeleOver K S) :=
    (numberFieldAdeleOver K S).algebra
  let algKR : Algebra K (numberFieldAdeleOver K S) := inferInstanceAs (Algebra K (Adeles K))
  let towerKR := @IsScalarTower.of_algebraMap_eq _ _ _ _ _ _ algAK algKR algAR
    (fun _ => rfl)
  let algBL : Algebra (upperCoefficients K L S) L :=
    (upperCoefficients K L S).toSubring.subtype.toAlgebra
  let algBE : Algebra (upperCoefficients K L S)
      (numberFieldAdeleOver L (numberFieldExceptionalPreimage (L := L) S)) :=
    (numberFieldAdeleOver L (numberFieldExceptionalPreimage (L := L) S)).algebra
  let algLE : Algebra L (numberFieldAdeleOver L (numberFieldExceptionalPreimage (L := L) S)) :=
    inferInstanceAs (Algebra L (Adeles L))
  let towerLE := @IsScalarTower.of_algebraMap_eq _ _ _ _ _ _ algBL algLE algBE
    (fun _ => rfl)
  apply (baseChangeRingPointsEquiv (upperCoefficients K L S) L
    (numberFieldAdeleOver L (numberFieldExceptionalPreimage (L := L) S)) X).injective
  rw [numberFieldSpaceWeilRestrictionPointsEquiv_apply,
    ringWeilRestrictionPointsEquiv_eq_evaluation K L (Adeles K) (Adeles L)
      (adeleInclusion (K := K) (L := L)) (adeleInclusion_compatible K L)
      (numberFieldAdeleTensorMap K L) (fun _ => by simp [numberFieldAdeleTensorMap])]
  have hc := spaceWeilRestrictionEvaluation_baseChange
    (lowerCoefficients K S) (upperCoefficients K L S) K L
    (numberFieldAdeleOver K S)
    (numberFieldAdeleOver L (numberFieldExceptionalPreimage (L := L) S))
    (isPullback_weilRestrictionTensor (lowerCoefficients K S) (upperCoefficients K L S) K L
      (numberFieldSIntegersFractionTensorEquiv K L S)
      (fun b => by simp only [numberFieldSIntegersFractionTensorEquiv_tmul, map_one, one_mul]; rfl))
    (adeleInclusion (K := K) (L := L))
    (NumberFieldFixedModelWeilEvaluation.adeleInclusion_compatible K L S)
    (adeleInclusion_compatible K L) X h
    (numberFieldSpaceGenericFiberEquiv K S _ p)
  have hrhs : baseChangeRingPointsEquiv (upperCoefficients K L S) L
      (numberFieldAdeleOver L (numberFieldExceptionalPreimage (L := L) S)) X
      (numberFieldSpaceGenericFiberEquiv L (numberFieldExceptionalPreimage (L := L) S) X
        (NumberFieldSpaceFixedModelWeilEvaluation.adelicEvaluation K L S X h p)) =
      NumberFieldSpaceFixedModelWeilEvaluation.adelicEvaluation K L S X h p := by
    exact (numberFieldSpaceGenericFiberEquiv L
      (numberFieldExceptionalPreimage (L := L) S) X).symm_apply_apply _
  rw [hrhs]
  refine hc.trans ?_
  change NumberFieldSpaceFixedModelWeilEvaluation.adelicEvaluation K L S X h
    ((numberFieldSpaceGenericFiberEquiv K S _).symm
      (numberFieldSpaceGenericFiberEquiv K S _ p)) = _
  rw [Equiv.symm_apply_apply]

variable (Y : AlgebraicSpace (Spec (CommRingCat.of L)))
  (hY : IsAlgebraicSpace _ ((ringWeilRestriction K L).obj Y.toSheaf))
  (e : numberFieldSpaceGenericFiber L (numberFieldExceptionalPreimage (L := L) S) X ≅ Y)

/-- The actual generic-fibre comparison followed by the specified upper-model identification. -/
def genericFiberIsoOfIso :
    numberFieldSpaceGenericFiber K S
      (ringWeilRestrictionSpace (lowerCoefficients K S) (upperCoefficients K L S) X h) ≅
      ringWeilRestrictionSpace K L Y hY :=
  (genericFiberIso K L S X h).trans
    (ObjectProperty.isoMk _
      ((ringWeilRestriction K L).mapIso ((forgetToSheaf _).mapIso e)))

/-- The generic-fibre original counit square also respects any upper-model identification. -/
theorem adelicEvaluation_modelOfIso
    (p : NumberFieldSpaceAdelePoints K S
      (ringWeilRestrictionSpace (lowerCoefficients K S) (upperCoefficients K L S) X h)) :
    numberFieldSpaceWeilRestrictionPointsEquiv K L Y hY
        (numberFieldSpaceSpreadEquiv K S
          (ringWeilRestrictionSpace (lowerCoefficients K S) (upperCoefficients K L S) X h) _
          (genericFiberIsoOfIso K L S X h Y hY e) p) =
      numberFieldSpaceSpreadEquiv L (numberFieldExceptionalPreimage (L := L) S) X Y e
        (NumberFieldSpaceFixedModelWeilEvaluation.adelicEvaluation K L S X h p) := by
  have hn := ringWeilRestrictionPointsEquivOfAlgEquiv_map
    (R := K) (R' := L) (A := Adeles K) (B := Adeles L)
    (h := genericWeilAlgebraic K L S X h) hY e.hom (numberFieldAdeleTensorEquiv K L)
    (numberFieldSpaceSpreadEquiv K S
      (ringWeilRestrictionSpace (lowerCoefficients K S) (upperCoefficients K L S) X h) _
      (genericFiberIso K L S X h) p)
  exact hn.trans (congrArg (RingPoints.map e.hom) (adelicEvaluation_model K L S X h p))

variable (hsep : IsSeparated X) (hft : FiniteTypeOverRing (upperCoefficients K L S) X)
  (hWsep : IsSeparated
    (ringWeilRestrictionSpace (lowerCoefficients K S) (upperCoefficients K L S) X h))
  (hWft : FiniteTypeOverRing (lowerCoefficients K S)
    (ringWeilRestrictionSpace (lowerCoefficients K S) (upperCoefficients K L S) X h))

/-- The full original Weil comparison is a homeomorphism for these specified generic-fibre models. -/
def adelicPointHomeomorphOfIso :
    @Homeomorph
      (NumberFieldSpaceFieldAdelePoints K (ringWeilRestrictionSpace K L Y hY))
      (NumberFieldSpaceFieldAdelePoints L Y)
      (numberFieldSpaceSpreadTopology K S
        (ringWeilRestrictionSpace (lowerCoefficients K S) (upperCoefficients K L S) X h) _
        (genericFiberIsoOfIso K L S X h Y hY e))
      (numberFieldSpaceSpreadTopology L (numberFieldExceptionalPreimage (L := L) S) X Y e) := by
  letI := numberFieldSpaceAdelePointTopology K S
    (ringWeilRestrictionSpace (lowerCoefficients K S) (upperCoefficients K L S) X h)
  letI := numberFieldSpaceAdelePointTopology L (numberFieldExceptionalPreimage (L := L) S) X
  letI := numberFieldSpaceSpreadTopology K S
    (ringWeilRestrictionSpace (lowerCoefficients K S) (upperCoefficients K L S) X h) _
    (genericFiberIsoOfIso K L S X h Y hY e)
  letI := numberFieldSpaceSpreadTopology L (numberFieldExceptionalPreimage (L := L) S) X Y e
  exact (numberFieldSpaceSpreadHomeomorph K S
    (ringWeilRestrictionSpace (lowerCoefficients K S) (upperCoefficients K L S) X h) _
    (genericFiberIsoOfIso K L S X h Y hY e)).symm.trans
    ((NumberFieldSpaceFixedModelWeilHomeomorph.adelicPointHomeomorph K L S X h
      hsep hft hWsep hWft).trans
      (numberFieldSpaceSpreadHomeomorph L (numberFieldExceptionalPreimage (L := L) S) X Y e))

/-- The generic-fibre homeomorphism has precisely the published canonical full tensor map. -/
@[simp]
theorem adelicPointHomeomorphOfIso_apply
    (x : NumberFieldSpaceFieldAdelePoints K (ringWeilRestrictionSpace K L Y hY)) :
    adelicPointHomeomorphOfIso K L S X h Y hY e hsep hft hWsep hWft x =
      numberFieldSpaceWeilRestrictionPointsEquiv K L Y hY x := by
  obtain ⟨p, rfl⟩ := (numberFieldSpaceSpreadEquiv K S
    (ringWeilRestrictionSpace (lowerCoefficients K S) (upperCoefficients K L S) X h) _
    (genericFiberIsoOfIso K L S X h Y hY e)).surjective x
  change numberFieldSpaceSpreadEquiv L (numberFieldExceptionalPreimage (L := L) S) X Y e
      (NumberFieldSpaceFixedModelWeilHomeomorph.adelicPointHomeomorph K L S X h hsep hft hWsep hWft
        ((numberFieldSpaceSpreadEquiv K S
          (ringWeilRestrictionSpace (lowerCoefficients K S) (upperCoefficients K L S) X h) _
          (genericFiberIsoOfIso K L S X h Y hY e)).symm
          (numberFieldSpaceSpreadEquiv K S
            (ringWeilRestrictionSpace (lowerCoefficients K S) (upperCoefficients K L S) X h) _
            (genericFiberIsoOfIso K L S X h Y hY e) p))) = _
  rw [Equiv.symm_apply_apply, NumberFieldSpaceFixedModelWeilHomeomorph.adelicPointHomeomorph_apply]
  exact (adelicEvaluation_modelOfIso K L S X h Y hY e p).symm

end Langlands.Global.NumberFieldSpaceWeilGenericFiber

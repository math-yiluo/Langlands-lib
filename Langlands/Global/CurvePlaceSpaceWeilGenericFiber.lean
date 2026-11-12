import Langlands.Global.CurvePlaceSpaceFixedModelWeilHomeomorph
import Langlands.Global.AdelicSpaceWeilRestrictionPoints
import Langlands.Global.CurvePlacePrincipalSIntegerFinite
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceWeilRestrictionBaseChangeEvaluation
import Langlands.Global.AdelicSpaceStageComparison

/-! # Original generic-fibre comparison of a curve-place space Weil model -/

noncomputable section

universe u

open CategoryTheory Topology IsDedekindDomain IntermediateField AlgebraicCurve
open _root_.AlgebraicGeometry
open scoped TensorProduct AlgebraicCurve.CurveModel IntermediateField.algebraAdjoinAdjoin
  Langlands.Global Langlands.Global.CurvePlacePrincipalSIntegers

namespace Langlands.Global.CurvePlaceSpaceWeilGenericFiber

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open CurvePlacePrincipalSIntegerSpaceWeilTopology (lowerCoefficients upperCoefficients)
open AdelicFunctoriality

set_option backward.isDefEq.respectTransparency false

variable (k K L : Type u) [Field k] [Finite k] [Field K] [Field L]
  [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
  [FiniteDimensional K L] (s : K) [FiniteDimensional k⟮s⟯ K]
  (t : CurveModel.chartRing k ({s} : Set K)) [Fact (t ≠ 0)]
  [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L] [FunctionField k L]
  (X : AlgebraicSpace (Spec (CommRingCat.of (upperCoefficients k K L s t))))
  (h : IsAlgebraicSpace _
    ((ringWeilRestriction (lowerCoefficients k K s t) (upperCoefficients k K L s t)).obj X.toSheaf))

include h in
omit [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L] [FunctionField k L] in
/-- The generic Weil sheaf is algebraic by the original fraction-field cartesian square. -/
theorem genericWeilAlgebraic : IsAlgebraicSpace _
    ((ringWeilRestriction K L).obj
      (curvePlaceSpaceGenericFiber k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))) X).toSheaf) :=
  isAlgebraicSpace_ringWeilRestriction_tensor (lowerCoefficients k K s t) (upperCoefficients k K L s t)
    K L (curvePlacePrincipalSIntegersFractionTensorEquiv k K L s t)
    (fun b => by simp only [curvePlacePrincipalSIntegersFractionTensorEquiv_tmul, map_one, one_mul]; rfl) X h

/-- The actual original integral Weil model has the expected generic fibre. -/
def genericFiberIso :
    curvePlaceSpaceGenericFiber k K (curvePlacePrincipalExceptional k K s (t : K))
      (ringWeilRestrictionSpace (lowerCoefficients k K s t) (upperCoefficients k K L s t) X h) ≅
      ringWeilRestrictionSpace K L
        (curvePlaceSpaceGenericFiber k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))) X)
        (genericWeilAlgebraic k K L s t X h) :=
  ringWeilRestrictionTensorBaseChangeIso (lowerCoefficients k K s t) (upperCoefficients k K L s t)
    K L (curvePlacePrincipalSIntegersFractionTensorEquiv k K L s t)
    (fun b => by simp only [curvePlacePrincipalSIntegersFractionTensorEquiv_tmul, map_one, one_mul]; rfl) X h

/-- The full inclusion retains the original field coefficients. -/
theorem adeleInclusion_compatible :
    (curvePlaceAdeleInclusion (k := k) (K := K) (L := L)).comp (algebraMap K (CurvePlaceAdeleRing k K)) =
      (algebraMap L (CurvePlaceAdeleRing k L)).comp (algebraMap K L) := by
  apply RingHom.ext
  intro a
  exact curvePlaceAdeleInclusion_diagonal (k := k) (K := K) (L := L) a

/-- The generic-fibre canonical adelic map is the original integral counit under both identifications. -/
theorem adelicEvaluation_model
    (p : CurvePlaceSpaceAdelePoints k K (curvePlacePrincipalExceptional k K s (t : K))
      (ringWeilRestrictionSpace (lowerCoefficients k K s t) (upperCoefficients k K L s t) X h)) :
    curvePlaceSpaceWeilRestrictionPointsEquiv k K L
        (curvePlaceSpaceGenericFiber k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))) X)
        (genericWeilAlgebraic k K L s t X h)
        (curvePlaceSpaceSpreadEquiv k K (curvePlacePrincipalExceptional k K s (t : K))
          (ringWeilRestrictionSpace (lowerCoefficients k K s t) (upperCoefficients k K L s t) X h) _
          (genericFiberIso k K L s t X h) p) =
      curvePlaceSpaceGenericFiberEquiv k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))) X
        (CurvePlaceSpaceFixedModelWeilEvaluation.adelicEvaluation k K L s t X h p) := by
  let algAK : Algebra (lowerCoefficients k K s t) K :=
    (lowerCoefficients k K s t).subtype.toAlgebra
  let algAR : Algebra (lowerCoefficients k K s t) (curvePlaceAdeleOver k K (curvePlacePrincipalExceptional k K s (t : K))) :=
    (curvePlaceAdeleOver k K (curvePlacePrincipalExceptional k K s (t : K))).algebra
  let algKR : Algebra K (curvePlaceAdeleOver k K (curvePlacePrincipalExceptional k K s (t : K))) := inferInstanceAs (Algebra K (CurvePlaceAdeleRing k K))
  let towerKR := @IsScalarTower.of_algebraMap_eq _ _ _ _ _ _ algAK algKR algAR
    (curvePlaceAdeleLevelDiagonal_eq k K (curvePlacePrincipalExceptional k K s (t : K)))
  let algBL : Algebra (upperCoefficients k K L s t) L :=
    (upperCoefficients k K L s t).subtype.toAlgebra
  let algBE : Algebra (upperCoefficients k K L s t)
      (curvePlaceAdeleOver k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))) :=
    (curvePlaceAdeleOver k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))).algebra
  let algLE : Algebra L (curvePlaceAdeleOver k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))) :=
    inferInstanceAs (Algebra L (CurvePlaceAdeleRing k L))
  let towerLE := @IsScalarTower.of_algebraMap_eq _ _ _ _ _ _ algBL algLE algBE
    (curvePlaceAdeleLevelDiagonal_eq k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))))
  apply (baseChangeRingPointsEquiv (upperCoefficients k K L s t) L
    (curvePlaceAdeleOver k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))) X).injective
  rw [curvePlaceSpaceWeilRestrictionPointsEquiv_apply,
    ringWeilRestrictionPointsEquiv_eq_evaluation K L (CurvePlaceAdeleRing k K) (CurvePlaceAdeleRing k L)
      (curvePlaceAdeleInclusion (k := k) (K := K) (L := L)) (adeleInclusion_compatible k K L)
      (curvePlaceAdeleTensorMap k K L) (fun _ => by simp [curvePlaceAdeleTensorMap])]
  have hc := spaceWeilRestrictionEvaluation_baseChange
    (lowerCoefficients k K s t) (upperCoefficients k K L s t) K L
    (curvePlaceAdeleOver k K (curvePlacePrincipalExceptional k K s (t : K)))
    (curvePlaceAdeleOver k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))))
    (isPullback_weilRestrictionTensor (lowerCoefficients k K s t) (upperCoefficients k K L s t) K L
      (curvePlacePrincipalSIntegersFractionTensorEquiv k K L s t)
      (fun b => by simp only [curvePlacePrincipalSIntegersFractionTensorEquiv_tmul, map_one, one_mul]; rfl))
    (curvePlaceAdeleInclusion (k := k) (K := K) (L := L))
    (CurvePlaceFixedModelWeilEvaluation.adeleInclusion_compatible k K L s t)
    (adeleInclusion_compatible k K L) X h
    (curvePlaceSpaceGenericFiberEquiv k K (curvePlacePrincipalExceptional k K s (t : K)) _ p)
  have hrhs : baseChangeRingPointsEquiv (upperCoefficients k K L s t) L
      (curvePlaceAdeleOver k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))) X
      (curvePlaceSpaceGenericFiberEquiv k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))) X
        (CurvePlaceSpaceFixedModelWeilEvaluation.adelicEvaluation k K L s t X h p)) =
      CurvePlaceSpaceFixedModelWeilEvaluation.adelicEvaluation k K L s t X h p := by
    exact (curvePlaceSpaceGenericFiberEquiv k L
      (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))) X).symm_apply_apply _
  rw [hrhs]
  refine hc.trans ?_
  change CurvePlaceSpaceFixedModelWeilEvaluation.adelicEvaluation k K L s t X h
    ((curvePlaceSpaceGenericFiberEquiv k K (curvePlacePrincipalExceptional k K s (t : K)) _).symm
      (curvePlaceSpaceGenericFiberEquiv k K (curvePlacePrincipalExceptional k K s (t : K)) _ p)) = _
  rw [Equiv.symm_apply_apply]

variable (Y : AlgebraicSpace (Spec (CommRingCat.of L)))
  (hY : IsAlgebraicSpace _ ((ringWeilRestriction K L).obj Y.toSheaf))
  (e : curvePlaceSpaceGenericFiber k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))) X ≅ Y)

/-- The actual generic-fibre comparison followed by the specified upper-model identification. -/
def genericFiberIsoOfIso :
    curvePlaceSpaceGenericFiber k K (curvePlacePrincipalExceptional k K s (t : K))
      (ringWeilRestrictionSpace (lowerCoefficients k K s t) (upperCoefficients k K L s t) X h) ≅
      ringWeilRestrictionSpace K L Y hY :=
  (genericFiberIso k K L s t X h).trans
    (ObjectProperty.isoMk _
      ((ringWeilRestriction K L).mapIso ((forgetToSheaf _).mapIso e)))

/-- The generic-fibre original counit square also respects any upper-model identification. -/
theorem adelicEvaluation_modelOfIso
    (p : CurvePlaceSpaceAdelePoints k K (curvePlacePrincipalExceptional k K s (t : K))
      (ringWeilRestrictionSpace (lowerCoefficients k K s t) (upperCoefficients k K L s t) X h)) :
    curvePlaceSpaceWeilRestrictionPointsEquiv k K L Y hY
        (curvePlaceSpaceSpreadEquiv k K (curvePlacePrincipalExceptional k K s (t : K))
          (ringWeilRestrictionSpace (lowerCoefficients k K s t) (upperCoefficients k K L s t) X h) _
          (genericFiberIsoOfIso k K L s t X h Y hY e) p) =
      curvePlaceSpaceSpreadEquiv k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))) X Y e
        (CurvePlaceSpaceFixedModelWeilEvaluation.adelicEvaluation k K L s t X h p) := by
  have hn := ringWeilRestrictionPointsEquivOfAlgEquiv_map
    (R := K) (R' := L) (A := CurvePlaceAdeleRing k K) (B := CurvePlaceAdeleRing k L)
    (h := genericWeilAlgebraic k K L s t X h) hY e.hom (curvePlaceAdeleTensorEquiv k K L)
    (curvePlaceSpaceSpreadEquiv k K (curvePlacePrincipalExceptional k K s (t : K))
      (ringWeilRestrictionSpace (lowerCoefficients k K s t) (upperCoefficients k K L s t) X h) _
      (genericFiberIso k K L s t X h) p)
  exact hn.trans (congrArg (RingPoints.map e.hom) (adelicEvaluation_model k K L s t X h p))

variable (hsep : IsSeparated X) (hft : FiniteTypeOverRing (upperCoefficients k K L s t) X)
  (hWsep : IsSeparated
    (ringWeilRestrictionSpace (lowerCoefficients k K s t) (upperCoefficients k K L s t) X h))
  (hWft : FiniteTypeOverRing (lowerCoefficients k K s t)
    (ringWeilRestrictionSpace (lowerCoefficients k K s t) (upperCoefficients k K L s t) X h))
  (hS : (curvePlacePrincipalExceptional k K s (t : K)).Nonempty)

/-- The full original Weil comparison is a homeomorphism for these specified generic-fibre models. -/
def adelicPointHomeomorphOfIso :
    @Homeomorph
      (CurvePlaceSpaceFieldAdelePoints k K (ringWeilRestrictionSpace K L Y hY))
      (CurvePlaceSpaceFieldAdelePoints k L Y)
      (curvePlaceSpaceSpreadTopology k K (curvePlacePrincipalExceptional k K s (t : K))
        (ringWeilRestrictionSpace (lowerCoefficients k K s t) (upperCoefficients k K L s t) X h) _
        (genericFiberIsoOfIso k K L s t X h Y hY e))
      (curvePlaceSpaceSpreadTopology k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))) X Y e) := by
  letI := curvePlaceSpaceAdelePointTopology k K (curvePlacePrincipalExceptional k K s (t : K))
    (ringWeilRestrictionSpace (lowerCoefficients k K s t) (upperCoefficients k K L s t) X h)
  letI := curvePlaceSpaceAdelePointTopology k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))) X
  letI := curvePlaceSpaceSpreadTopology k K (curvePlacePrincipalExceptional k K s (t : K))
    (ringWeilRestrictionSpace (lowerCoefficients k K s t) (upperCoefficients k K L s t) X h) _
    (genericFiberIsoOfIso k K L s t X h Y hY e)
  letI := curvePlaceSpaceSpreadTopology k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))) X Y e
  exact (curvePlaceSpaceSpreadHomeomorph k K (curvePlacePrincipalExceptional k K s (t : K))
    (ringWeilRestrictionSpace (lowerCoefficients k K s t) (upperCoefficients k K L s t) X h) _
    (genericFiberIsoOfIso k K L s t X h Y hY e)).symm.trans
    ((CurvePlaceSpaceFixedModelWeilHomeomorph.adelicPointHomeomorph k K L s t X h
      hsep hft hWsep hWft hS).trans
      (curvePlaceSpaceSpreadHomeomorph k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))) X Y e))

/-- The generic-fibre homeomorphism has precisely the published canonical full tensor map. -/
@[simp]
theorem adelicPointHomeomorphOfIso_apply
    (x : CurvePlaceSpaceFieldAdelePoints k K (ringWeilRestrictionSpace K L Y hY)) :
    adelicPointHomeomorphOfIso k K L s t X h Y hY e hsep hft hWsep hWft hS x =
      curvePlaceSpaceWeilRestrictionPointsEquiv k K L Y hY x := by
  obtain ⟨p, rfl⟩ := (curvePlaceSpaceSpreadEquiv k K (curvePlacePrincipalExceptional k K s (t : K))
    (ringWeilRestrictionSpace (lowerCoefficients k K s t) (upperCoefficients k K L s t) X h) _
    (genericFiberIsoOfIso k K L s t X h Y hY e)).surjective x
  change curvePlaceSpaceSpreadEquiv k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))) X Y e
      (CurvePlaceSpaceFixedModelWeilHomeomorph.adelicPointHomeomorph k K L s t X h hsep hft hWsep hWft hS
        ((curvePlaceSpaceSpreadEquiv k K (curvePlacePrincipalExceptional k K s (t : K))
          (ringWeilRestrictionSpace (lowerCoefficients k K s t) (upperCoefficients k K L s t) X h) _
          (genericFiberIsoOfIso k K L s t X h Y hY e)).symm
          (curvePlaceSpaceSpreadEquiv k K (curvePlacePrincipalExceptional k K s (t : K))
            (ringWeilRestrictionSpace (lowerCoefficients k K s t) (upperCoefficients k K L s t) X h) _
            (genericFiberIsoOfIso k K L s t X h Y hY e) p))) = _
  rw [Equiv.symm_apply_apply, CurvePlaceSpaceFixedModelWeilHomeomorph.adelicPointHomeomorph_apply]
  exact (adelicEvaluation_modelOfIso k K L s t X h Y hY e p).symm

end Langlands.Global.CurvePlaceSpaceWeilGenericFiber

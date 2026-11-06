import Langlands.Global.CurvePlaceFixedModelWeilHomeomorph
import Langlands.Global.CurvePlaceAdeleInclusion

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology IsDedekindDomain IntermediateField AlgebraicCurve
open _root_.AlgebraicGeometry
open scoped AlgebraicCurve.CurveModel IntermediateField.algebraAdjoinAdjoin
  Langlands.Global Langlands.Global.CurvePlacePrincipalSIntegers
  Langlands.Global.CurvePlaceIntegralTopology

namespace Langlands.Global.CurvePlaceFixedModelWeilEvaluation

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.PointTopology
open CurvePlaceFixedLevelWeilEvaluation

set_option backward.isDefEq.respectTransparency false

section Projections

variable (k F : Type u) [Field k] [Field F] [Algebra k F]
  (S : Finset (Place k F))

/-- The literal projection from full curve adeles to an original completed field. -/
def fullFieldProjection (v : Place k F) :
    curvePlaceAdeleOver k F S →ₐ[curvePlaceSIntegers k F S] curvePlaceCompletion v :=
  { toRingHom := RestrictedProduct.evalRingHom (fun w => curvePlaceCompletion w) v
    commutes' := fun _ => rfl }

/-- All original completed-field projections of the actual full adele ring. -/
def fullFieldProduct : curvePlaceAdeleOver k F S →ₐ[curvePlaceSIntegers k F S]
    ∀ v : Place k F, curvePlaceCompletion v :=
  AlgHom.pi (fullFieldProjection k F S)

/-- Original completed-field coordinates determine every full curve adele. -/
theorem fullFieldProduct_injective : Function.Injective (fullFieldProduct k F S) := by
  intro a b h
  apply RestrictedProduct.ext
  intro v
  exact congrFun h v

variable (Y : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
  [IsSeparated Y.hom] [QuasiSeparatedSpace Y.left]

/-- Completed-field coordinates determine actual full-adele points of a separated model. -/
theorem full_point_ext (p q : CurvePlaceFixedModelAdelePoints k F S Y)
    (h : ∀ v : Place k F, p.changeRing (fullFieldProjection k F S v) =
      q.changeRing (fullFieldProjection k F S v)) : p = q := by
  let : IsReduced (curvePlaceAdeleOver k F S) :=
    isReduced_of_injective (fullFieldProduct k F S) (fullFieldProduct_injective k F S)
  apply schemeSeparatedCoefficientInjectivity_proof (curvePlaceSIntegers k F S)
    (curvePlaceAdeleOver k F S) (∀ v : Place k F, curvePlaceCompletion v) Y
    (fullFieldProduct k F S) (fullFieldProduct_injective k F S)
  apply productPointMap_injective (curvePlaceSIntegers k F S)
    (fun v : Place k F => curvePlaceCompletion v) Y
  funext v
  apply RingPoint.ext
  change Spec.map _ ≫ (Spec.map _ ≫ p.left) = Spec.map _ ≫ (Spec.map _ ≫ q.left)
  rw [← Category.assoc, ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
  exact congrArg (fun x => x.left) (h v)

omit [IsSeparated Y.hom] [QuasiSeparatedSpace Y.left] in
/-- Inclusion of an arithmetic stage preserves every original completed-field coordinate. -/
theorem stage_pointField (T : AdelicLevelIndexAbove S)
    (p : RingPoint (curvePlaceSIntegers k F S) Y (curvePlaceAdeleLevelOver k F S T))
    (v : Place k F) :
    (p.changeRing (curvePlaceAdeleLevelOverι k F S T).hom).changeRing
        (fullFieldProjection k F S v) = p.changeRing (fieldProjection k F S T v) := by
  apply RingPoint.ext
  change Spec.map _ ≫ (Spec.map _ ≫ p.left) = Spec.map _ ≫ p.left
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

end Projections

variable (k K L : Type u) [Field k] [Finite k] [Field K] [Field L]
  [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
  [FiniteDimensional K L] (s : K) [FiniteDimensional k⟮s⟯ K]
  (t : CurveModel.chartRing k ({s} : Set K)) [Fact (t ≠ 0)]

omit [FiniteDimensional k⟮s⟯ K] [Fact (t ≠ 0)] in
/-- The literal full inclusion retains both original integral coefficient actions. -/
theorem adeleInclusion_compatible :
    (curvePlaceAdeleInclusion (k := k) (K := K) (L := L)).comp
        (algebraMap (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceAdeleOver k K (curvePlacePrincipalExceptional k K s (t : K)))) =
      (algebraMap (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))) (curvePlaceAdeleOver k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))))).comp
        (algebraMap (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))))) := by
  apply RingHom.ext
  intro a
  apply RestrictedProduct.ext
  intro q
  exact curvePlaceCompletionInclusion_algebraMap q a.val

/-- Evaluate an original lower full adele in an original upper completed field. -/
def fullUpperFieldCoefficient (v : Place k K) (q : CurvePlacesAbove k L v) :
    (curvePlaceAdeleOver k K (curvePlacePrincipalExceptional k K s (t : K))) →+* curvePlaceCompletion q.1 :=
  (CurvePlaceCompletionExtension.completionMap v q).comp
    (fullFieldProjection k K (curvePlacePrincipalExceptional k K s (t : K)) v).toRingHom

omit [FiniteDimensional k⟮s⟯ K] [Fact (t ≠ 0)] in
/-- Full completed-field evaluation retains both original integral bases. -/
theorem fullUpperFieldCoefficient_compatible (v : Place k K) (q : CurvePlacesAbove k L v) :
    (fullUpperFieldCoefficient k K L s t v q).comp (algebraMap (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceAdeleOver k K (curvePlacePrincipalExceptional k K s (t : K)))) =
      (algebraMap (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))) (curvePlaceCompletion q.1)).comp
        (algebraMap (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))))) := by
  apply RingHom.ext
  intro a
  exact CurvePlaceCompletionExtension.completionMap_algebraMap v q a.val

omit [FiniteDimensional k⟮s⟯ K] [Fact (t ≠ 0)] in
/-- Original upper-field evaluation is the corresponding coordinate of the literal full inclusion. -/
theorem fullUpperFieldCoefficient_eq_projection (v : Place k K) (q : CurvePlacesAbove k L v) :
    fullUpperFieldCoefficient k K L s t v q =
      (fullFieldProjection k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))) q.1).toRingHom.comp
        (curvePlaceAdeleInclusion (k := k) (K := K) (L := L)) := by
  apply RingHom.ext
  intro a
  exact (curvePlaceAdeleInclusion_apply_above a v q).symm

variable (Y : Over (Spec (CommRingCat.of (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))))))) [LocallyOfFiniteType Y.hom]

/-- The original integral Weil counit evaluated along the literal full curve adele inclusion. -/
def adelicEvaluation (p : CurvePlaceFixedModelAdelePoints k K (curvePlacePrincipalExceptional k K s (t : K))
    (affineChartWeilRestriction (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))) Y)) :
    CurvePlaceFixedModelAdelePoints k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))) Y :=
  weilRestrictionEvaluation (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))) (curvePlaceAdeleOver k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceAdeleOver k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))))
    (curvePlaceAdeleInclusion (k := k) (K := K) (L := L))
    (adeleInclusion_compatible k K L s t) Y p

/-- The full counit's coordinate is canonical evaluation in the original upper completed field. -/
theorem adelicEvaluation_field (p : CurvePlaceFixedModelAdelePoints k K (curvePlacePrincipalExceptional k K s (t : K))
    (affineChartWeilRestriction (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))) Y))
    (v : Place k K) (q : CurvePlacesAbove k L v) :
    (adelicEvaluation k K L s t Y p).changeRing (fullFieldProjection k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))) q.1) =
      weilRestrictionEvaluation (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))) (curvePlaceAdeleOver k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceCompletion q.1)
        (fullUpperFieldCoefficient k K L s t v q)
        (fullUpperFieldCoefficient_compatible k K L s t v q) Y p := by
  exact weilRestrictionEvaluation_natural_upper (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))) (curvePlaceAdeleOver k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceAdeleOver k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))))
    (curvePlaceCompletion q.1)
    (curvePlaceAdeleInclusion (k := k) (K := K) (L := L))
    (fullUpperFieldCoefficient k K L s t v q)
    (adeleInclusion_compatible k K L s t) (fullUpperFieldCoefficient_compatible k K L s t v q)
    (fullFieldProjection k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))) q.1)
    (fullUpperFieldCoefficient_eq_projection k K L s t v q).symm Y p

/-- On an original stage point, full evaluation restricts to the original stage evaluation. -/
theorem adelicEvaluation_stage_field (T : AdelicLevelIndexAbove (curvePlacePrincipalExceptional k K s (t : K)))
    (p : RingPoint (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (affineChartWeilRestriction (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))) Y)
      (curvePlaceAdeleLevelOver k K (curvePlacePrincipalExceptional k K s (t : K)) T))
    (v : Place k K) (q : CurvePlacesAbove k L v) :
    (adelicEvaluation k K L s t Y
      (p.changeRing (curvePlaceAdeleLevelOverι k K (curvePlacePrincipalExceptional k K s (t : K)) T).hom)).changeRing
        (fullFieldProjection k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))) q.1) =
      fieldEvaluation k K L s t T Y v q p := by
  rw [adelicEvaluation_field]
  exact weilRestrictionEvaluation_natural_lower (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))))
    (curvePlaceAdeleLevelOver k K (curvePlacePrincipalExceptional k K s (t : K)) T) (curvePlaceAdeleOver k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceCompletion q.1)
    (upperFieldCoefficient k K L s t T v q) (fullUpperFieldCoefficient k K L s t v q)
    (upperFieldCoefficient_compatible k K L s t T v q)
    (fullUpperFieldCoefficient_compatible k K L s t v q)
    (curvePlaceAdeleLevelOverι k K (curvePlacePrincipalExceptional k K s (t : K)) T).hom (RingHom.ext fun _ => rfl) Y p

variable [CompactSpace Y.left] (n : ℕ) (j : Y.left ⟶ ProjectiveSpace (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))) n)
  [IsImmersion j] (hj : j ≫ projectiveSpaceToSpec (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))) n = Y.hom)

/-- On every original arithmetic stage, the full homeomorphism is the original integral counit. -/
theorem adelicPointHomeomorph_stage_eq_evaluation (T : AdelicLevelIndexAbove (curvePlacePrincipalExceptional k K s (t : K)))
    (p : RingPoint (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (affineChartWeilRestriction (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))) Y)
      (curvePlaceAdeleLevelOver k K (curvePlacePrincipalExceptional k K s (t : K)) T)) :
    CurvePlaceFixedModelWeilHomeomorph.adelicPointHomeomorph k K L s t Y n j hj
        (p.changeRing (curvePlaceAdeleLevelOverι k K (curvePlacePrincipalExceptional k K s (t : K)) T).hom) =
      adelicEvaluation k K L s t Y
        (p.changeRing (curvePlaceAdeleLevelOverι k K (curvePlacePrincipalExceptional k K s (t : K)) T).hom) := by
  let : IsSeparated Y.hom := isSeparated_of_projectiveImmersion _ Y n j hj
  let : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  rw [CurvePlaceFixedModelWeilHomeomorph.adelicPointHomeomorph_stage]
  apply full_point_ext k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))) Y
  intro q₀
  let v := curvePlaceRestriction (K := K) q₀
  let q : CurvePlacesAbove k L v := ⟨q₀, rfl⟩
  exact (stage_pointField k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))) Y
      (CurvePlacePrincipalSIntegerFixedLevelRegroup.upperLevel k K L s t T)
      (CurvePlacePrincipalSIntegerFixedLevelRegroup.adelicLevelPointHomeomorph
        k K L s t T Y n j hj p) q₀).trans
    ((levelPoint_fieldEvaluation_at k K L s t T Y n j hj p v q).trans
      (adelicEvaluation_stage_field k K L s t Y T p v q).symm)

/-- The full original fixed-model curve homeomorphism evaluates the original Weil counit. -/
theorem adelicPointHomeomorph_eq_evaluation
    (p : CurvePlaceFixedModelAdelePoints k K (curvePlacePrincipalExceptional k K s (t : K))
      (affineChartWeilRestriction (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))) Y)) :
    CurvePlaceFixedModelWeilHomeomorph.adelicPointHomeomorph k K L s t Y n j hj p =
      adelicEvaluation k K L s t Y p := by
  obtain ⟨T, q, rfl⟩ :=
    ((curvePlaceFixedModelPointComparisonProperties k K (curvePlacePrincipalExceptional k K s (t : K))
      (affineChartWeilRestriction (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))) Y)).2 inferInstance).1 p
  exact adelicPointHomeomorph_stage_eq_evaluation k K L s t Y n j hj T q

end Langlands.Global.CurvePlaceFixedModelWeilEvaluation

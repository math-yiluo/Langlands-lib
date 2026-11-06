import Langlands.Global.CurvePlacePrincipalSIntegerFixedLevelRegroup
import Langlands.AlgebraicGeometry.PointTopology.WeilRestrictionEvaluation
import Langlands.AlgebraicGeometry.PointTopology.SchemeSeparatedCoefficientProofs

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology IsDedekindDomain IntermediateField AlgebraicCurve
open _root_.AlgebraicGeometry
open scoped TensorProduct AlgebraicCurve.CurveModel IntermediateField.algebraAdjoinAdjoin
  Langlands.Global Langlands.Global.FixedModelLocalProduct
  Langlands.Global.CurvePlacePrincipalSIntegers
  Langlands.Global.CurvePlacePrincipalSIntegerFixedLevelWeil
  Langlands.Global.CurvePlacePrincipalSIntegerLocalTensor
  Langlands.Global.CurvePlaceCompletionExtension
  Langlands.Global.CurvePlaceCompletedIntegersExtension
  Langlands.Global.CurvePlaceIntegralTopology

namespace Langlands.Global.CurvePlaceFixedLevelWeilEvaluation

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.PointTopology
open CurvePlacePrincipalSIntegerFixedLevelWeil CurvePlacePrincipalSIntegerFixedLevelRegroup

set_option backward.isDefEq.respectTransparency false

section Projections

variable (k F : Type u) [Field k] [Field F] [Algebra k F]
  (S : Finset (Place k F)) (T : AdelicLevelIndexAbove S)

/-- The literal projection of an enlarged level to any original completed field. -/
def fieldProjection (v : Place k F) :
    curvePlaceAdeleLevelOver k F S T →ₐ[curvePlaceSIntegers k F S]
      curvePlaceCompletion v :=
  { toRingHom := (RestrictedProduct.evalRingHom (fun w => curvePlaceCompletion w) v).comp
      (curvePlaceAdeleLevel k F T.val).subtype
    commutes' := fun _ => rfl }

/-- The original enlarged level embeds into the product of all original completed fields. -/
def fieldProduct : curvePlaceAdeleLevelOver k F S T →ₐ[curvePlaceSIntegers k F S]
    ∀ v : Place k F, curvePlaceCompletion v :=
  AlgHom.pi (fieldProjection k F S T)

/-- No coefficient is lost by passing to all completed-field coordinates. -/
theorem fieldProduct_injective : Function.Injective (fieldProduct k F S T) := by
  intro a b h
  apply Subtype.ext
  apply RestrictedProduct.ext
  intro v
  exact congrFun h v

variable (Y : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
  [IsSeparated Y.hom] [QuasiSeparatedSpace Y.left]

/-- Points of a separated original model are determined by all original completed-field coordinates. -/
theorem point_ext (p q : RingPoint (curvePlaceSIntegers k F S) Y
    (curvePlaceAdeleLevelOver k F S T))
    (h : ∀ v : Place k F, p.changeRing (fieldProjection k F S T v) =
      q.changeRing (fieldProjection k F S T v)) : p = q := by
  let : IsReduced (curvePlaceAdeleLevelOver k F S T) :=
    isReduced_of_injective (fieldProduct k F S T) (fieldProduct_injective k F S T)
  apply schemeSeparatedCoefficientInjectivity_proof (curvePlaceSIntegers k F S)
    (curvePlaceAdeleLevelOver k F S T) (∀ v : Place k F, curvePlaceCompletion v) Y
    (fieldProduct k F S T) (fieldProduct_injective k F S T)
  apply productPointMap_injective (curvePlaceSIntegers k F S)
    (fun v : Place k F => curvePlaceCompletion v) Y
  funext v
  apply RingPoint.ext
  change Spec.map _ ≫ (Spec.map _ ≫ p.left) = Spec.map _ ≫ (Spec.map _ ≫ q.left)
  rw [← Category.assoc, ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
  exact congrArg (fun x => x.left) (h v)

end Projections

variable (k K L : Type u) [Field k] [Finite k] [Field K] [Field L]
  [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
  [FiniteDimensional K L] (s : K) [FiniteDimensional k⟮s⟯ K]
  (t : CurveModel.chartRing k ({s} : Set K)) [Fact (t ≠ 0)]
  (T : AdelicLevelIndexAbove (curvePlacePrincipalExceptional k K s (t : K)))

/-- The original lower level evaluated at one original upper completed field. -/
def upperFieldCoefficient (p : Place k K) (q : CurvePlacesAbove k L p) :
    curvePlaceAdeleLevelOver k K (curvePlacePrincipalExceptional k K s (t : K)) T →+*
      curvePlaceCompletion q.1 :=
  (CurvePlaceCompletionExtension.completionMap p q).comp
    (fieldProjection k K (curvePlacePrincipalExceptional k K s (t : K)) T p).toRingHom

omit [FiniteDimensional k⟮s⟯ K] [Fact (t ≠ 0)] in
/-- The completed-field evaluation retains both original integral coefficient maps. -/
theorem upperFieldCoefficient_compatible (p : Place k K) (q : CurvePlacesAbove k L p) :
    (upperFieldCoefficient k K L s t T p q).comp
        (algebraMap (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K)))
          (curvePlaceAdeleLevelOver k K (curvePlacePrincipalExceptional k K s (t : K)) T)) =
      (algebraMap (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
          (curvePlacePrincipalExceptional k K s (t : K)))) (curvePlaceCompletion q.1)).comp
        (algebraMap (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K)))
          (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
            (curvePlacePrincipalExceptional k K s (t : K))))) := by
  apply RingHom.ext
  intro a
  change CurvePlaceCompletionExtension.completionMap p q
      (algebraMap K (curvePlaceCompletion p) a.val) =
    algebraMap L (curvePlaceCompletion q.1) (algebraMap K L a.val)
  exact CurvePlaceCompletionExtension.completionMap_algebraMap p q a.val

/-- Include an original upper local factor in its original completed field. -/
def upperFactorFieldAlgHom (i : CurvePlaceLevelFactorIndex k K T.val)
    (q : Above k K L s t T i) :
    upperFactor k K L s t T i q →ₐ[
      curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
        (curvePlacePrincipalExceptional k K s (t : K)))] curvePlaceCompletion q.1 := by
  cases i with
  | inl p => exact AlgHom.id _ _
  | inr p =>
    letI : Fact (p.1 ∉ curvePlacePrincipalExceptional k K s (t : K)) := ⟨fun h => p.2 (T.property h)⟩
    refine { (curvePlaceCompletionIntegers q.1).subtype with commutes' := ?_ }
    intro b
    exact CurvePlacePrincipalSIntegerLocalTensor.upperMap_coe k K s t p.1 L b q

variable (Y : Over (Spec (CommRingCat.of
    (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))))))

omit [FiniteDimensional k⟮s⟯ K] [Fact (t ≠ 0)] in
/-- Regrouping retains the original underlying scheme morphism. -/
theorem factorPointHomeomorph_left (z : Σ i, Above k K L s t T i)
    (x : RingPoint (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y
      (upperFactor k K L s t T z.1 z.2)) :
    HEq (CurvePlacePrincipalSIntegerFixedLevelRegroup.factorPointHomeomorph k K L s t T Y z x).left
      x.left := by
  rcases z with ⟨i, q⟩
  cases i <;> rfl

/-- The original whole lower-level coefficient map into one original tensor factor. -/
def localCoefficient (i : CurvePlaceLevelFactorIndex k K T.val)
    (q : Above k K L s t T i) : (curvePlaceAdeleLevelOver k K (curvePlacePrincipalExceptional k K s (t : K)) T) →+* upperFactor k K L s t T i q :=
  (algebraMap (CurvePlaceLevelFactor k K T.val i) (upperFactor k K L s t T i q)).comp
    (levelFactorAlgHom k K s t T i).toRingHom

omit [FiniteDimensional k⟮s⟯ K] [Fact (t ≠ 0)] in
/-- The original local coefficient map respects the two original integral bases. -/
theorem localCoefficient_compatible (i : CurvePlaceLevelFactorIndex k K T.val)
    (q : Above k K L s t T i) :
    (localCoefficient k K L s t T i q).comp (algebraMap (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceAdeleLevelOver k K (curvePlacePrincipalExceptional k K s (t : K)) T)) =
      (algebraMap (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) (upperFactor k K L s t T i q)).comp (algebraMap (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K))))) := by
  apply RingHom.ext
  intro a
  cases i with
  | inl p =>
    change CurvePlaceCompletionExtension.completionMap p.1 q
        (algebraMap K (curvePlaceCompletion p.1) a.val) =
      algebraMap L (curvePlaceCompletion q.1) (algebraMap K L a.val)
    exact CurvePlaceCompletionExtension.completionMap_algebraMap p.1 q a.val
  | inr p =>
    apply Subtype.ext
    change CurvePlaceCompletionExtension.completionMap p.1 q
        (algebraMap K (curvePlaceCompletion p.1) a.val) =
      algebraMap L (curvePlaceCompletion q.1) (algebraMap K L a.val)
    exact CurvePlaceCompletionExtension.completionMap_algebraMap p.1 q a.val

omit [FiniteDimensional k⟮s⟯ K] [Fact (t ≠ 0)] in
/-- Including a local tensor factor in its field recovers the original whole-level field coefficient. -/
theorem upperFactorFieldAlgHom_localCoefficient (i : CurvePlaceLevelFactorIndex k K T.val)
    (q : Above k K L s t T i) :
    (upperFactorFieldAlgHom k K L s t T i q).toRingHom.comp
        (localCoefficient k K L s t T i q) =
      upperFieldCoefficient k K L s t T (lowerPlace k K s t T i) q := by
  apply RingHom.ext
  intro a
  cases i <;> rfl

variable [LocallyOfFiniteType Y.hom]

/-- The original local counit, followed into its field, is evaluation on the original whole level. -/
theorem localPointMap_fieldEvaluation
    (p : RingPoint (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (affineChartWeilRestriction (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y) (curvePlaceAdeleLevelOver k K (curvePlacePrincipalExceptional k K s (t : K)) T))
    (i : CurvePlaceLevelFactorIndex k K T.val) (q : Above k K L s t T i) :
    (completedTensorWeilRestrictionPointMap (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) (CurvePlaceLevelFactor k K T.val i)
      (upperFactor k K L s t T i) (tensorEquiv k K L s t T i)
      (tensorEquiv_one_tmul k K L s t T i) Y
      (p.changeRing (levelFactorAlgHom k K s t T i)) q).changeRing
        (upperFactorFieldAlgHom k K L s t T i q) =
      weilRestrictionEvaluation (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) (curvePlaceAdeleLevelOver k K (curvePlacePrincipalExceptional k K s (t : K)) T) (curvePlaceCompletion q.1)
        (upperFieldCoefficient k K L s t T (lowerPlace k K s t T i) q)
        (upperFieldCoefficient_compatible k K L s t T (lowerPlace k K s t T i) q) Y p := by
  rw [completedTensorWeilRestrictionPointMap_eq_evaluation (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) (curvePlaceAdeleLevelOver k K (curvePlacePrincipalExceptional k K s (t : K)) T)
    (CurvePlaceLevelFactor k K T.val i) (upperFactor k K L s t T i)
    (tensorEquiv k K L s t T i) (tensorEquiv_one_tmul k K L s t T i)
    (levelFactorAlgHom k K s t T i) q (localCoefficient k K L s t T i q)
    (localCoefficient_compatible k K L s t T i q) rfl Y p]
  exact weilRestrictionEvaluation_natural_upper (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) (curvePlaceAdeleLevelOver k K (curvePlacePrincipalExceptional k K s (t : K)) T)
    (upperFactor k K L s t T i q) (curvePlaceCompletion q.1)
    (localCoefficient k K L s t T i q)
    (upperFieldCoefficient k K L s t T (lowerPlace k K s t T i) q)
    (localCoefficient_compatible k K L s t T i q)
    (upperFieldCoefficient_compatible k K L s t T (lowerPlace k K s t T i) q)
    (upperFactorFieldAlgHom k K L s t T i q)
    (upperFactorFieldAlgHom_localCoefficient k K L s t T i q) Y p

variable [CompactSpace Y.left] [QuasiSeparatedSpace Y.left] (n : ℕ)
  (j : Y.left ⟶ ProjectiveSpace (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) n) [IsImmersion j]
  (hj : j ≫ projectiveSpaceToSpec (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) n = Y.hom)

/-- Every original upper completed-field coordinate is the original local counit followed into its field. -/
theorem levelPoint_fieldCoordinate
    (p : RingPoint (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (affineChartWeilRestriction (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y) (curvePlaceAdeleLevelOver k K (curvePlacePrincipalExceptional k K s (t : K)) T))
    (i : CurvePlaceLevelFactorIndex k K T.val) (q : Above k K L s t T i) :
    (CurvePlacePrincipalSIntegerFixedLevelRegroup.adelicLevelPointHomeomorph k K L s t T Y n j hj p).changeRing
        (fieldProjection k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))) (upperLevel k K L s t T) q.1) =
      (completedTensorWeilRestrictionPointMap (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) (CurvePlaceLevelFactor k K T.val i)
      (upperFactor k K L s t T i) (tensorEquiv k K L s t T i)
      (tensorEquiv_one_tmul k K L s t T i) Y
      (p.changeRing (levelFactorAlgHom k K s t T i)) q).changeRing (upperFactorFieldAlgHom k K L s t T i q) := by
  have hco := CurvePlacePrincipalSIntegerFixedLevelRegroup.adelicLevelPointHomeomorph_coordinate_left
    k K L s t T Y n j hj p ⟨i, q⟩
  have hc := CurvePlacePrincipalSIntegerFixedLevelWeil.levelPointHomeomorph_component
    k K L s t T Y n j hj p i q
  cases i with
  | inl v =>
    have hleft := hco.trans
      ((eq_of_heq (factorPointHomeomorph_left k K L s t T Y ⟨(.inl v), q⟩
        (CurvePlacePrincipalSIntegerFixedLevelWeil.levelPointHomeomorph
          k K L s t T Y n j hj p ⟨(.inl v), q⟩))).trans
        (congrArg (fun x => x.left) hc))
    apply RingPoint.ext
    change Spec.map (CommRingCat.ofHom
        (fieldProjection k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))) (upperLevel k K L s t T) q.1).toRingHom) ≫ (CurvePlacePrincipalSIntegerFixedLevelRegroup.adelicLevelPointHomeomorph k K L s t T Y n j hj p).left =
      Spec.map (CommRingCat.ofHom (upperFactorFieldAlgHom k K L s t T (.inl v) q).toRingHom) ≫ (completedTensorWeilRestrictionPointMap (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) (CurvePlaceLevelFactor k K T.val (.inl v))
      (upperFactor k K L s t T (.inl v)) (tensorEquiv k K L s t T (.inl v))
      (tensorEquiv_one_tmul k K L s t T (.inl v)) Y
      (p.changeRing (levelFactorAlgHom k K s t T (.inl v))) q).left
    erw [← hleft]
    rw [← Category.assoc, ← Spec.map_comp]
    rfl
  | inr v =>
    have hleft := hco.trans
      ((eq_of_heq (factorPointHomeomorph_left k K L s t T Y ⟨(.inr v), q⟩
        (CurvePlacePrincipalSIntegerFixedLevelWeil.levelPointHomeomorph
          k K L s t T Y n j hj p ⟨(.inr v), q⟩))).trans
        (congrArg (fun x => x.left) hc))
    apply RingPoint.ext
    change Spec.map (CommRingCat.ofHom
        (fieldProjection k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))) (upperLevel k K L s t T) q.1).toRingHom) ≫ (CurvePlacePrincipalSIntegerFixedLevelRegroup.adelicLevelPointHomeomorph k K L s t T Y n j hj p).left =
      Spec.map (CommRingCat.ofHom (upperFactorFieldAlgHom k K L s t T (.inr v) q).toRingHom) ≫ (completedTensorWeilRestrictionPointMap (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) (CurvePlaceLevelFactor k K T.val (.inr v))
      (upperFactor k K L s t T (.inr v)) (tensorEquiv k K L s t T (.inr v))
      (tensorEquiv_one_tmul k K L s t T (.inr v)) Y
      (p.changeRing (levelFactorAlgHom k K s t T (.inr v))) q).left
    erw [← hleft]
    rw [← Category.assoc, ← Spec.map_comp]
    rfl

/-- The original upper field coordinate of the finite-level Weil map is its canonical whole-level evaluation. -/
theorem levelPoint_fieldEvaluation
    (p : RingPoint (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (affineChartWeilRestriction (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y) (curvePlaceAdeleLevelOver k K (curvePlacePrincipalExceptional k K s (t : K)) T))
    (i : CurvePlaceLevelFactorIndex k K T.val) (q : Above k K L s t T i) :
    (CurvePlacePrincipalSIntegerFixedLevelRegroup.adelicLevelPointHomeomorph k K L s t T Y n j hj p).changeRing
        (fieldProjection k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))) (upperLevel k K L s t T) q.1) =
      weilRestrictionEvaluation (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) (curvePlaceAdeleLevelOver k K (curvePlacePrincipalExceptional k K s (t : K)) T) (curvePlaceCompletion q.1)
        (upperFieldCoefficient k K L s t T (lowerPlace k K s t T i) q)
        (upperFieldCoefficient_compatible k K L s t T (lowerPlace k K s t T i) q) Y p :=
  (levelPoint_fieldCoordinate k K L s t T Y n j hj p i q).trans
    (localPointMap_fieldEvaluation k K L s t T Y p i q)

/-- Canonical evaluation of an original fixed-model level point in one original upper completed field. -/
def fieldEvaluation (v : Place k K) (q : CurvePlacesAbove k L v)
    (p : RingPoint (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (affineChartWeilRestriction (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y) (curvePlaceAdeleLevelOver k K (curvePlacePrincipalExceptional k K s (t : K)) T)) :
    RingPoint (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y (curvePlaceCompletion q.1) :=
  weilRestrictionEvaluation (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) (curvePlaceAdeleLevelOver k K (curvePlacePrincipalExceptional k K s (t : K)) T) (curvePlaceCompletion q.1)
    (upperFieldCoefficient k K L s t T v q)
    (upperFieldCoefficient_compatible k K L s t T v q) Y p

/-- The original upper field coordinate can be indexed by its actual place rather than a varying level index. -/
theorem levelPoint_fieldEvaluation_at
    (p : RingPoint (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (affineChartWeilRestriction (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y) (curvePlaceAdeleLevelOver k K (curvePlacePrincipalExceptional k K s (t : K)) T))
    (v : Place k K) (q : CurvePlacesAbove k L v) :
    (CurvePlacePrincipalSIntegerFixedLevelRegroup.adelicLevelPointHomeomorph k K L s t T Y n j hj p).changeRing (fieldProjection k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))) (upperLevel k K L s t T) q.1) =
      fieldEvaluation k K L s t T Y v q p := by
  classical
  by_cases hv : v ∈ T.val
  · exact levelPoint_fieldEvaluation k K L s t T Y n j hj p (.inl ⟨v, hv⟩) q
  · exact levelPoint_fieldEvaluation k K L s t T Y n j hj p (.inr ⟨v, hv⟩) q

variable (U : AdelicLevelIndexAbove (curvePlacePrincipalExceptional k K s (t : K))) (hTU : T ≤ U)

/-- The literal upper coefficient inclusion between full-preimage levels over the original upper base. -/
def upperTransition :
    curvePlaceAdeleLevelOver k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))) (upperLevel k K L s t T) →ₐ[(curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K))))]
      curvePlaceAdeleLevelOver k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))) (upperLevel k K L s t U) :=
  (curvePlaceAdeleLevelOverMap k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))) (show upperLevel k K L s t T ≤ upperLevel k K L s t U from
    fun q hq => (mem_curvePlaceExceptionalPreimage U.val q).mpr
      (hTU ((mem_curvePlaceExceptionalPreimage T.val q).mp hq)))).hom

omit [FiniteDimensional k⟮s⟯ K] [Fact (t ≠ 0)]
  [LocallyOfFiniteType Y.hom] [CompactSpace Y.left] [QuasiSeparatedSpace Y.left] in
/-- Every literal upper completed-field coordinate commutes with the original upper support inclusion. -/
theorem upperTransition_pointField
    (x : RingPoint (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y
      (curvePlaceAdeleLevelOver k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))) (upperLevel k K L s t T)))
    (q : Place k L) :
    (x.changeRing (upperTransition k K L s t T U hTU)).changeRing
        (fieldProjection k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))) (upperLevel k K L s t U) q) =
      x.changeRing (fieldProjection k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))) (upperLevel k K L s t T) q) := by
  apply RingPoint.ext
  change Spec.map _ ≫ (Spec.map _ ≫ x.left) = Spec.map _ ≫ x.left
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

omit [CompactSpace Y.left] [QuasiSeparatedSpace Y.left] in
/-- Canonical upper-field evaluation is independent of enlarging the original lower support. -/
theorem fieldEvaluation_natural
    (p : RingPoint (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (affineChartWeilRestriction (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y) (curvePlaceAdeleLevelOver k K (curvePlacePrincipalExceptional k K s (t : K)) T))
    (v : Place k K) (q : CurvePlacesAbove k L v) :
    fieldEvaluation k K L s t U Y v q
        (p.changeRing (curvePlaceAdeleLevelOverMap k K (curvePlacePrincipalExceptional k K s (t : K)) hTU).hom) =
      fieldEvaluation k K L s t T Y v q p :=
  weilRestrictionEvaluation_natural_lower (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) (curvePlaceAdeleLevelOver k K (curvePlacePrincipalExceptional k K s (t : K)) T) (curvePlaceAdeleLevelOver k K (curvePlacePrincipalExceptional k K s (t : K)) U) (curvePlaceCompletion q.1)
    (upperFieldCoefficient k K L s t T v q) (upperFieldCoefficient k K L s t U v q)
    (upperFieldCoefficient_compatible k K L s t T v q)
    (upperFieldCoefficient_compatible k K L s t U v q)
    (curvePlaceAdeleLevelOverMap k K (curvePlacePrincipalExceptional k K s (t : K)) hTU).hom (RingHom.ext fun _ => rfl) Y p

/-- The two actual fixed-model Weil level homeomorphisms commute with the two literal support inclusions. -/
theorem levelPoint_natural
    (p : RingPoint (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (affineChartWeilRestriction (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y) (curvePlaceAdeleLevelOver k K (curvePlacePrincipalExceptional k K s (t : K)) T)) :
    (CurvePlacePrincipalSIntegerFixedLevelRegroup.adelicLevelPointHomeomorph k K L s t U Y n j hj
      (p.changeRing (curvePlaceAdeleLevelOverMap k K (curvePlacePrincipalExceptional k K s (t : K)) hTU).hom)) = (CurvePlacePrincipalSIntegerFixedLevelRegroup.adelicLevelPointHomeomorph k K L s t T Y n j hj p).changeRing (upperTransition k K L s t T U hTU) := by
  let : IsSeparated Y.hom := isSeparated_of_projectiveImmersion (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) Y n j hj
  apply point_ext k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))) (upperLevel k K L s t U) Y
  intro q₀
  let v := curvePlaceRestriction (K := K) q₀
  let q : CurvePlacesAbove k L v := ⟨q₀, rfl⟩
  exact (levelPoint_fieldEvaluation_at k K L s t U Y n j hj
      (p.changeRing (curvePlaceAdeleLevelOverMap k K (curvePlacePrincipalExceptional k K s (t : K)) hTU).hom) v q).trans
    ((fieldEvaluation_natural k K L s t T Y U hTU p v q).trans
      ((levelPoint_fieldEvaluation_at k K L s t T Y n j hj p v q).symm.trans
        (upperTransition_pointField k K L s t T Y U hTU (CurvePlacePrincipalSIntegerFixedLevelRegroup.adelicLevelPointHomeomorph k K L s t T Y n j hj p) q₀).symm))

end Langlands.Global.CurvePlaceFixedLevelWeilEvaluation

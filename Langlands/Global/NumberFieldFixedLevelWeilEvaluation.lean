import Langlands.Global.NumberFieldSIntegerFixedLevelRegroup
import Langlands.AlgebraicGeometry.PointTopology.WeilRestrictionEvaluation
import Langlands.AlgebraicGeometry.PointTopology.SchemeSeparatedCoefficientProofs

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology IsDedekindDomain
open _root_.AlgebraicGeometry
open scoped NumberField TensorProduct NumberField.LiesOver
  Langlands.Global Langlands.Global.NumberFieldSIntegers
  Langlands.Global.NumberFieldSIntegerLocalTensor
  Langlands.Global.NumberFieldSIntegerLevelWeil
  Langlands.Global.NumberFieldSIntegerFixedLevelWeil
  Langlands.Global.FixedModelLocalProduct
  Langlands.Global.AdelicFunctoriality.FiniteExtension
  Langlands.Global.AdelicFunctoriality.InfiniteExtension
  Langlands.Global.AdelicFunctoriality.IntegralTensor
  Langlands.Global.AdelicFunctoriality.IntegralTopology

namespace Langlands.Global.NumberFieldFixedLevelWeilEvaluation

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.PointTopology
open AdelicFunctoriality NumberFieldSIntegerLevelWeil
  NumberFieldSIntegerFixedLevelWeil NumberFieldSIntegerFixedLevelRegroup

set_option backward.isDefEq.respectTransparency false

section Projections

variable (K : Type u) [Field K] [NumberField K]

/-- All original infinite and finite places, without a support-dependent index. -/
abbrev OriginalPlace := NumberFieldPlace K

/-- The original completed field at any original place. -/
abbrev OriginalCompletion : OriginalPlace K → Type u
  | .inl v => v.Completion
  | .inr v => v.adicCompletion K

instance completionField (v : OriginalPlace K) : Field (OriginalCompletion K v) := by
  cases v <;> dsimp [OriginalCompletion] <;> infer_instance

/-- The original global field embedded in its original completed field. -/
def fieldCoefficient : (v : OriginalPlace K) → K →+* OriginalCompletion K v
  | .inl v => algebraMap K v.Completion
  | .inr v => algebraMap K (v.adicCompletion K)

variable (S : Finset (FinitePlace K)) (T : AdelicLevelIndexAbove S)

instance completionAlgebra (v : OriginalPlace K) :
    Algebra ((S : Set (FinitePlace K)).integer K) (OriginalCompletion K v) := by
  cases v <;> dsimp [OriginalCompletion] <;> infer_instance

/-- The literal projection from the enlarged level to any original completed field. -/
def fieldProjection (v : OriginalPlace K) :
    (numberFieldAdeleLevelOver K S T) →ₐ[((S : Set (FinitePlace K)).integer K)] OriginalCompletion K v := by
  cases v with
  | inl v =>
    exact { toRingHom := (infiniteProjection K v).comp (numberFieldAdeleLevel K T.val).subtype
            commutes' := fun _ => rfl }
  | inr v =>
    exact { toRingHom := (finiteProjection K v).comp (numberFieldAdeleLevel K T.val).subtype
            commutes' := fun _ => rfl }

/-- The enlarged level in the product of all its original completed fields. -/
def fieldProduct : (numberFieldAdeleLevelOver K S T) →ₐ[((S : Set (FinitePlace K)).integer K)]
    ∀ v : OriginalPlace K, OriginalCompletion K v :=
  AlgHom.pi (fieldProjection K S T)

/-- The original infinite and finite coordinates determine every coefficient. -/
theorem fieldProduct_injective : Function.Injective (fieldProduct K S T) := by
  intro a b h
  apply Subtype.ext
  apply Prod.ext
  · funext v
    exact congrFun h (.inl v)
  · apply RestrictedProduct.ext
    intro v
    exact congrFun h (.inr v)

variable (Y : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
  [IsSeparated Y.hom] [QuasiSeparatedSpace Y.left]

/-- Points of a separated original model are determined by all original field coordinates. -/
theorem point_ext (p q : RingPoint ((S : Set (FinitePlace K)).integer K) Y (numberFieldAdeleLevelOver K S T))
    (h : ∀ v : OriginalPlace K, p.changeRing (fieldProjection K S T v) =
      q.changeRing (fieldProjection K S T v)) : p = q := by
  let : IsReduced (numberFieldAdeleLevelOver K S T) :=
    isReduced_of_injective (fieldProduct K S T) (fieldProduct_injective K S T)
  apply schemeSeparatedCoefficientInjectivity_proof ((S : Set (FinitePlace K)).integer K) (numberFieldAdeleLevelOver K S T)
    (∀ v : OriginalPlace K, OriginalCompletion K v) Y
    (fieldProduct K S T) (fieldProduct_injective K S T)
  apply productPointMap_injective ((S : Set (FinitePlace K)).integer K)
    (fun v : OriginalPlace K => OriginalCompletion K v) Y
  funext v
  apply RingPoint.ext
  change Spec.map _ ≫ (Spec.map _ ≫ p.left) = Spec.map _ ≫ (Spec.map _ ≫ q.left)
  rw [← Category.assoc, ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
  exact congrArg (fun x => x.left) (h v)

end Projections

variable (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] (S : Finset (FinitePlace K)) (T : AdelicLevelIndexAbove S)

/-- Original upper places above one original lower place. -/
abbrev PlacesAbove : OriginalPlace K → Type u
  | .inl v => InfinitePlacesAbove L v
  | .inr v => FinitePlacesAbove L v

/-- The actual upper place carried by a place-above witness. -/
def upperPlace : (v : OriginalPlace K) → PlacesAbove K L v → OriginalPlace L
  | .inl _, q => .inl q.1
  | .inr _, q => .inr q.1

/-- The original lower completion embedding into one original upper completion. -/
def completionCoefficient : (v : OriginalPlace K) → (q : PlacesAbove K L v) →
    OriginalCompletion K v →+* OriginalCompletion L (upperPlace K L v q)
  | .inl v, q => NumberField.LiesOver.completionMap (v := v) (w := q.1)
  | .inr v, q => FiniteExtension.completionMap v q.1

/-- Completion embeddings retain the original global field coefficients at every place. -/
theorem completionCoefficient_algebraMap (v : OriginalPlace K) (q : PlacesAbove K L v)
    (a : K) :
    completionCoefficient K L v q (fieldCoefficient K v a) =
      fieldCoefficient L (upperPlace K L v q) (algebraMap K L a) := by
  cases v with
  | inl v =>
    change NumberField.LiesOver.completionMap (v := v) (w := q.1)
      (algebraMap K v.Completion a) = algebraMap L q.1.Completion (algebraMap K L a)
    exact NumberField.LiesOver.completionMap_coe (v := v) (w := q.1)
      (WithAbs.toAbs v.1 a)
  | inr v => exact FiniteExtension.completionMap_coe v q.1 a

/-- The original lower level evaluated in one original upper completed field. -/
def upperFieldCoefficient (v : OriginalPlace K) (q : PlacesAbove K L v) :
    (numberFieldAdeleLevelOver K S T) →+* OriginalCompletion L (upperPlace K L v q) :=
  (completionCoefficient K L v q).comp (fieldProjection K S T v).toRingHom

/-- The completed-field coefficient retains both original integral bases. -/
theorem upperFieldCoefficient_compatible (v : OriginalPlace K) (q : PlacesAbove K L v) :
    (upperFieldCoefficient K L S T v q).comp (algebraMap ((S : Set (FinitePlace K)).integer K) (numberFieldAdeleLevelOver K S T)) =
      (algebraMap (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) (OriginalCompletion L (upperPlace K L v q))).comp
        (algebraMap ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L)) := by
  apply RingHom.ext
  intro a
  cases v with
  | inl v => exact completionCoefficient_algebraMap K L (.inl v) q a.val
  | inr v => exact completionCoefficient_algebraMap K L (.inr v) q a.val

/-- The original place of a lower level factor. -/
def lowerPlace : NumberFieldLevelFactorIndex K T.val → OriginalPlace K
  | .inl v => .inl v
  | .inr (.inl v) => .inr v.1
  | .inr (.inr v) => .inr v.1

/-- The same actual upper-place witness, with the support-dependent branch removed. -/
def abovePlace : (i : NumberFieldLevelFactorIndex K T.val) →
    Above K L T.val i → PlacesAbove K L (lowerPlace K S T i)
  | .inl _, q => q
  | .inr (.inl _), q => q
  | .inr (.inr _), q => q

/-- Include each original upper local factor in its original completed field. -/
def upperFactorFieldAlgHom (i : NumberFieldLevelFactorIndex K T.val)
    (q : Above K L T.val i) :
    upperFactor K L T.val i q →ₐ[(((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L)]
      OriginalCompletion L (upperPlace K L (lowerPlace K S T i) (abovePlace K L S T i q)) := by
  cases i with
  | inl v => exact AlgHom.id _ _
  | inr z =>
    cases z with
    | inl v => exact AlgHom.id _ _
    | inr v =>
      letI : Fact (v.1 ∉ S) := ⟨fun h => v.2 (T.property h)⟩
      refine { (q.1.adicCompletionIntegers L).subtype with commutes' := ?_ }
      intro b
      exact NumberFieldSIntegerLocalTensor.upperMap_coe K S v.1 L b q

variable (Y : Over (Spec (CommRingCat.of (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L))))

private theorem transported_refl_apply {I : Type*} (P : I → Type*)
    (τ : ∀ i, TopologicalSpace (P i)) {C : Type*} (f : ∀ i, P i → C)
    {a b : I} (h : a = b)
    (e : @Homeomorph (P b) (P a) (τ b) (τ a) =
      @Homeomorph (P b) (P b) (τ b) (τ b)) (x : P b) :
    f a ((Eq.mpr e (@Homeomorph.refl (P b) (τ b))) x) = f b x := by
  cases h
  cases e
  rfl

set_option maxHeartbeats 400000 in
/-- Regrouping preserves the original underlying scheme morphism. -/
theorem factorPointHomeomorph_left (z : Σ i, Above K L T.val i)
    (x : RingPoint (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y (upperFactor K L T.val z.1 z.2)) :
    HEq (NumberFieldSIntegerFixedLevelRegroup.factorPointHomeomorph K L S T Y z x).left
      x.left := by
  rcases z with ⟨i, q⟩
  cases i with
  | inl v =>
    dsimp only [NumberFieldSIntegerFixedLevelRegroup.factorPointHomeomorph,
      NumberFieldSIntegerFixedLevelRegroup.indexEquiv,
      NumberFieldSIntegerLevelRegroup.indexEquiv, NumberFieldSIntegerLevelRegroup.indexMap,
      upperFactor, NumberFieldLevelFactor, NumberFieldSIntegerLevelWeil.upperCommRing,
      NumberFieldSIntegerLevelWeil.upperTopology, instAdelicLevelModelPoints6,
      instAdelicLevelModelPoints7] at *
    apply heq_of_eq
    refine transported_refl_apply (C := Spec (CommRingCat.of q.1.Completion) ⟶ Y.left)
      (fun a : Algebra (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) q.1.Completion =>
        letI := a; RingPoint (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y q.1.Completion)
      (fun a => letI := a; schemePointTopology (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y q.1.Completion)
      (fun (a : Algebra (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) q.1.Completion) => letI : Algebra (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) q.1.Completion := a; fun p : RingPoint (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y q.1.Completion => p.left)
      (show FixedModelLocalProduct.numberFieldFactorAlgebra L
        (numberFieldExceptionalPreimage (L := L) S) (upperLevel K L S T)
        (indexEquiv K L S T ⟨.inl v, q⟩) =
        NumberFieldSIntegerFixedLevelWeil.upperCoefficientAlgebra K L S T (.inl v) q
        from Algebra.algebra_ext _ _ fun _ => rfl) ?_ x
  | inr z =>
    cases z with
    | inl v =>
      dsimp only [NumberFieldSIntegerFixedLevelRegroup.factorPointHomeomorph,
      NumberFieldSIntegerFixedLevelRegroup.indexEquiv,
      NumberFieldSIntegerLevelRegroup.indexEquiv, NumberFieldSIntegerLevelRegroup.indexMap,
      upperFactor, NumberFieldLevelFactor, NumberFieldSIntegerLevelWeil.upperCommRing,
      NumberFieldSIntegerLevelWeil.upperTopology, instAdelicLevelModelPoints6,
      instAdelicLevelModelPoints7] at *
      apply heq_of_eq
      refine transported_refl_apply (C := Spec (CommRingCat.of (q.1.adicCompletion L)) ⟶ Y.left)
        (fun a : Algebra (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) (q.1.adicCompletion L) =>
          letI := a; RingPoint (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y (q.1.adicCompletion L))
        (fun a => letI := a; schemePointTopology (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y (q.1.adicCompletion L))
        (fun (a : Algebra (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) (q.1.adicCompletion L)) => letI : Algebra (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) (q.1.adicCompletion L) := a; fun p : RingPoint (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y (q.1.adicCompletion L) => p.left)
        (show FixedModelLocalProduct.numberFieldFactorAlgebra L
          (numberFieldExceptionalPreimage (L := L) S) (upperLevel K L S T)
          (indexEquiv K L S T ⟨.inr (.inl v), q⟩) =
          NumberFieldSIntegerFixedLevelWeil.upperCoefficientAlgebra K L S T (.inr (.inl v)) q
          from Algebra.algebra_ext _ _ fun _ => rfl) ?_ x
    | inr v =>
      dsimp only [NumberFieldSIntegerFixedLevelRegroup.factorPointHomeomorph,
      NumberFieldSIntegerFixedLevelRegroup.indexEquiv,
      NumberFieldSIntegerLevelRegroup.indexEquiv, NumberFieldSIntegerLevelRegroup.indexMap,
      upperFactor, NumberFieldLevelFactor, NumberFieldSIntegerLevelWeil.upperCommRing,
      NumberFieldSIntegerLevelWeil.upperTopology, instAdelicLevelModelPoints6,
      instAdelicLevelModelPoints7] at *
      apply heq_of_eq
      refine transported_refl_apply (C := Spec (CommRingCat.of (q.1.adicCompletionIntegers L)) ⟶ Y.left)
        (fun a : Algebra (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) (q.1.adicCompletionIntegers L) =>
          letI := a; RingPoint (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y (q.1.adicCompletionIntegers L))
        (fun a => letI := a; schemePointTopology (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y (q.1.adicCompletionIntegers L))
        (fun (a : Algebra (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) (q.1.adicCompletionIntegers L)) => letI : Algebra (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) (q.1.adicCompletionIntegers L) := a; fun p : RingPoint (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y (q.1.adicCompletionIntegers L) => p.left)
        (show FixedModelLocalProduct.numberFieldFactorAlgebra L
          (numberFieldExceptionalPreimage (L := L) S) (upperLevel K L S T)
          (indexEquiv K L S T ⟨.inr (.inr v), q⟩) =
          NumberFieldSIntegerFixedLevelWeil.upperCoefficientAlgebra K L S T (.inr (.inr v)) q
          from Algebra.algebra_ext _ _ fun _ => rfl) ?_ x

/-- The literal lower-level projection followed by the original local coefficient map. -/
def localCoefficient (i : NumberFieldLevelFactorIndex K T.val)
    (q : Above K L T.val i) : (numberFieldAdeleLevelOver K S T) →+* upperFactor K L T.val i q :=
  (algebraMap (NumberFieldLevelFactor K T.val i) (upperFactor K L T.val i q)).comp
    (levelFactorAlgHom K S T i).toRingHom

/-- The local coefficient maps respect both unchanged integral bases. -/
theorem localCoefficient_compatible (i : NumberFieldLevelFactorIndex K T.val)
    (q : Above K L T.val i) :
    (localCoefficient K L S T i q).comp (algebraMap ((S : Set (FinitePlace K)).integer K) (numberFieldAdeleLevelOver K S T)) =
      (algebraMap (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) (upperFactor K L T.val i q)).comp
        (algebraMap ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L)) := by
  apply RingHom.ext
  intro a
  cases i with
  | inl v => exact completionCoefficient_algebraMap K L (.inl v) q a.val
  | inr z =>
    cases z with
    | inl v => exact completionCoefficient_algebraMap K L (.inr v.1) q a.val
    | inr v =>
      apply Subtype.ext
      exact completionCoefficient_algebraMap K L (.inr v.1) q a.val

/-- Including the local factor in its field recovers whole-level field evaluation. -/
theorem upperFactorFieldAlgHom_localCoefficient (i : NumberFieldLevelFactorIndex K T.val)
    (q : Above K L T.val i) :
    (upperFactorFieldAlgHom K L S T i q).toRingHom.comp (localCoefficient K L S T i q) =
      upperFieldCoefficient K L S T (lowerPlace K S T i) (abovePlace K L S T i q) := by
  apply RingHom.ext
  intro a
  cases i with
  | inl _ => rfl
  | inr z => cases z <;> rfl

variable [LocallyOfFiniteType Y.hom]

/-- The original local counit, followed into its field, is evaluation on the original whole level. -/
theorem localPointMap_fieldEvaluation
    (p : RingPoint ((S : Set (FinitePlace K)).integer K) (affineChartWeilRestriction ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y) (numberFieldAdeleLevelOver K S T))
    (i : NumberFieldLevelFactorIndex K T.val) (q : Above K L T.val i) :
    (completedTensorWeilRestrictionPointMap ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) (NumberFieldLevelFactor K T.val i)
      (upperFactor K L T.val i) (tensorEquiv K L S T i)
      (tensorEquiv_one_tmul K L S T i) Y
      (p.changeRing (levelFactorAlgHom K S T i)) q).changeRing
        (upperFactorFieldAlgHom K L S T i q) =
      weilRestrictionEvaluation ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) (numberFieldAdeleLevelOver K S T) (OriginalCompletion L (upperPlace K L (lowerPlace K S T i) (abovePlace K L S T i q)))
        (upperFieldCoefficient K L S T (lowerPlace K S T i) (abovePlace K L S T i q))
        (upperFieldCoefficient_compatible K L S T (lowerPlace K S T i) (abovePlace K L S T i q)) Y p := by
  rw [completedTensorWeilRestrictionPointMap_eq_evaluation ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) (numberFieldAdeleLevelOver K S T)
    (NumberFieldLevelFactor K T.val i) (upperFactor K L T.val i)
    (tensorEquiv K L S T i) (tensorEquiv_one_tmul K L S T i)
    (levelFactorAlgHom K S T i) q (localCoefficient K L S T i q)
    (localCoefficient_compatible K L S T i q) rfl Y p]
  exact weilRestrictionEvaluation_natural_upper ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) (numberFieldAdeleLevelOver K S T)
    (upperFactor K L T.val i q) (OriginalCompletion L (upperPlace K L (lowerPlace K S T i) (abovePlace K L S T i q)))
    (localCoefficient K L S T i q)
    (upperFieldCoefficient K L S T (lowerPlace K S T i) (abovePlace K L S T i q))
    (localCoefficient_compatible K L S T i q)
    (upperFieldCoefficient_compatible K L S T (lowerPlace K S T i) (abovePlace K L S T i q))
    (upperFactorFieldAlgHom K L S T i q)
    (upperFactorFieldAlgHom_localCoefficient K L S T i q) Y p

/-- Canonical evaluation of an original fixed-model point in an original upper completed field. -/
def fieldEvaluation (v : OriginalPlace K) (q : PlacesAbove K L v)
    (p : RingPoint ((S : Set (FinitePlace K)).integer K) (affineChartWeilRestriction ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y) (numberFieldAdeleLevelOver K S T)) :
    RingPoint (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y (OriginalCompletion L (upperPlace K L v q)) :=
  weilRestrictionEvaluation ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) (numberFieldAdeleLevelOver K S T) (OriginalCompletion L (upperPlace K L v q))
    (upperFieldCoefficient K L S T v q)
    (upperFieldCoefficient_compatible K L S T v q) Y p

variable [CompactSpace Y.left] [QuasiSeparatedSpace Y.left] (n : ℕ)
  (j : Y.left ⟶ ProjectiveSpace (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) n) [IsImmersion j]
  (hj : j ≫ projectiveSpaceToSpec (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) n = Y.hom)


/-- Each original upper field coordinate is its local counit followed into the completed field. -/
theorem levelPoint_fieldCoordinate
    (p : RingPoint ((S : Set (FinitePlace K)).integer K) (affineChartWeilRestriction ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y) (numberFieldAdeleLevelOver K S T))
    (i : NumberFieldLevelFactorIndex K T.val) (q : Above K L T.val i) :
    (NumberFieldSIntegerFixedLevelRegroup.adelicLevelPointHomeomorph K L S T Y n j hj p).changeRing
        (fieldProjection L (numberFieldExceptionalPreimage (L := L) S) (upperLevel K L S T)
          (upperPlace K L (lowerPlace K S T i) (abovePlace K L S T i q))) =
      (completedTensorWeilRestrictionPointMap ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) (NumberFieldLevelFactor K T.val i)
      (upperFactor K L T.val i) (tensorEquiv K L S T i)
      (tensorEquiv_one_tmul K L S T i) Y
      (p.changeRing (levelFactorAlgHom K S T i)) q).changeRing (upperFactorFieldAlgHom K L S T i q) := by
  have hco := NumberFieldSIntegerFixedLevelRegroup.adelicLevelPointHomeomorph_coordinate_left
    K L S T Y n j hj p ⟨i, q⟩
  have hc := NumberFieldSIntegerFixedLevelWeil.levelPointHomeomorph_component
    K L S T Y n j hj p i q
  cases i with
  | inl v =>
    have hleft := hco.trans
      ((eq_of_heq (factorPointHomeomorph_left K L S T Y ⟨(.inl v), q⟩
        (NumberFieldSIntegerFixedLevelWeil.levelPointHomeomorph
          K L S T Y n j hj p ⟨(.inl v), q⟩))).trans
        (congrArg (fun x => x.left) hc))
    apply RingPoint.ext
    change Spec.map (CommRingCat.ofHom
        (fieldProjection L (numberFieldExceptionalPreimage (L := L) S) (upperLevel K L S T)
          (upperPlace K L (lowerPlace K S T (.inl v)) (abovePlace K L S T (.inl v) q))).toRingHom) ≫
        (NumberFieldSIntegerFixedLevelRegroup.adelicLevelPointHomeomorph K L S T Y n j hj p).left =
      Spec.map (CommRingCat.ofHom (upperFactorFieldAlgHom K L S T (.inl v) q).toRingHom) ≫
        (completedTensorWeilRestrictionPointMap ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) (NumberFieldLevelFactor K T.val (.inl v))
          (upperFactor K L T.val (.inl v)) (tensorEquiv K L S T (.inl v))
          (tensorEquiv_one_tmul K L S T (.inl v)) Y
          (p.changeRing (levelFactorAlgHom K S T (.inl v))) q).left
    erw [← hleft]
    rw [← Category.assoc, ← Spec.map_comp]
    rfl
  | inr z =>
    cases z with
    | inl v =>
      have hleft := hco.trans
        ((eq_of_heq (factorPointHomeomorph_left K L S T Y ⟨(.inr (.inl v)), q⟩
          (NumberFieldSIntegerFixedLevelWeil.levelPointHomeomorph
            K L S T Y n j hj p ⟨(.inr (.inl v)), q⟩))).trans
          (congrArg (fun x => x.left) hc))
      apply RingPoint.ext
      change Spec.map (CommRingCat.ofHom
          (fieldProjection L (numberFieldExceptionalPreimage (L := L) S) (upperLevel K L S T)
            (upperPlace K L (lowerPlace K S T (.inr (.inl v))) (abovePlace K L S T (.inr (.inl v)) q))).toRingHom) ≫
          (NumberFieldSIntegerFixedLevelRegroup.adelicLevelPointHomeomorph K L S T Y n j hj p).left =
        Spec.map (CommRingCat.ofHom (upperFactorFieldAlgHom K L S T (.inr (.inl v)) q).toRingHom) ≫
          (completedTensorWeilRestrictionPointMap ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) (NumberFieldLevelFactor K T.val (.inr (.inl v)))
            (upperFactor K L T.val (.inr (.inl v))) (tensorEquiv K L S T (.inr (.inl v)))
            (tensorEquiv_one_tmul K L S T (.inr (.inl v))) Y
            (p.changeRing (levelFactorAlgHom K S T (.inr (.inl v)))) q).left
      erw [← hleft]
      rw [← Category.assoc, ← Spec.map_comp]
      rfl
    | inr v =>
      have hleft := hco.trans
        ((eq_of_heq (factorPointHomeomorph_left K L S T Y ⟨(.inr (.inr v)), q⟩
          (NumberFieldSIntegerFixedLevelWeil.levelPointHomeomorph
            K L S T Y n j hj p ⟨(.inr (.inr v)), q⟩))).trans
          (congrArg (fun x => x.left) hc))
      apply RingPoint.ext
      change Spec.map (CommRingCat.ofHom
          (fieldProjection L (numberFieldExceptionalPreimage (L := L) S) (upperLevel K L S T)
            (upperPlace K L (lowerPlace K S T (.inr (.inr v))) (abovePlace K L S T (.inr (.inr v)) q))).toRingHom) ≫
          (NumberFieldSIntegerFixedLevelRegroup.adelicLevelPointHomeomorph K L S T Y n j hj p).left =
        Spec.map (CommRingCat.ofHom (upperFactorFieldAlgHom K L S T (.inr (.inr v)) q).toRingHom) ≫
          (completedTensorWeilRestrictionPointMap ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) (NumberFieldLevelFactor K T.val (.inr (.inr v)))
            (upperFactor K L T.val (.inr (.inr v))) (tensorEquiv K L S T (.inr (.inr v)))
            (tensorEquiv_one_tmul K L S T (.inr (.inr v))) Y
            (p.changeRing (levelFactorAlgHom K S T (.inr (.inr v)))) q).left
      erw [← hleft]
      rw [← Category.assoc, ← Spec.map_comp]
      rfl

/-- The finite-level Weil map has the canonical whole-level evaluation as every original field coordinate. -/
theorem levelPoint_fieldEvaluation
    (p : RingPoint ((S : Set (FinitePlace K)).integer K) (affineChartWeilRestriction ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y) (numberFieldAdeleLevelOver K S T))
    (i : NumberFieldLevelFactorIndex K T.val) (q : Above K L T.val i) :
    (NumberFieldSIntegerFixedLevelRegroup.adelicLevelPointHomeomorph K L S T Y n j hj p).changeRing
        (fieldProjection L (numberFieldExceptionalPreimage (L := L) S) (upperLevel K L S T)
          (upperPlace K L (lowerPlace K S T i) (abovePlace K L S T i q))) =
      fieldEvaluation K L S T Y (lowerPlace K S T i) (abovePlace K L S T i q) p :=
  (levelPoint_fieldCoordinate K L S T Y n j hj p i q).trans
    (localPointMap_fieldEvaluation K L S T Y p i q)

/-- An upper field coordinate can be indexed by its actual place, independently of the support. -/
theorem levelPoint_fieldEvaluation_at
    (p : RingPoint ((S : Set (FinitePlace K)).integer K) (affineChartWeilRestriction ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y) (numberFieldAdeleLevelOver K S T))
    (v : OriginalPlace K) (q : PlacesAbove K L v) :
    (NumberFieldSIntegerFixedLevelRegroup.adelicLevelPointHomeomorph K L S T Y n j hj p).changeRing
        (fieldProjection L (numberFieldExceptionalPreimage (L := L) S) (upperLevel K L S T)
          (upperPlace K L v q)) = fieldEvaluation K L S T Y v q p := by
  classical
  cases v with
  | inl v => exact levelPoint_fieldEvaluation K L S T Y n j hj p (.inl v) q
  | inr v =>
    by_cases hv : v ∈ T.val
    · exact levelPoint_fieldEvaluation K L S T Y n j hj p (.inr (.inl ⟨v, hv⟩)) q
    · exact levelPoint_fieldEvaluation K L S T Y n j hj p (.inr (.inr ⟨v, hv⟩)) q


variable (U : AdelicLevelIndexAbove S) (hTU : T ≤ U)

/-- The literal upper coefficient inclusion between full-preimage levels over the original upper base. -/
def upperTransition :
    numberFieldAdeleLevelOver L (numberFieldExceptionalPreimage (L := L) S) (upperLevel K L S T) →ₐ[(((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L)]
      numberFieldAdeleLevelOver L (numberFieldExceptionalPreimage (L := L) S) (upperLevel K L S U) :=
  (numberFieldAdeleLevelOverMap L (numberFieldExceptionalPreimage (L := L) S)
    (show upperLevel K L S T ≤ upperLevel K L S U from
      fun q hq => (mem_numberFieldExceptionalPreimage U.val q).mpr
        (hTU ((mem_numberFieldExceptionalPreimage T.val q).mp hq)))).hom

omit [LocallyOfFiniteType Y.hom] [CompactSpace Y.left] [QuasiSeparatedSpace Y.left] in
/-- Every original upper field coordinate commutes with the literal upper support inclusion. -/
theorem upperTransition_pointField
    (x : RingPoint (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y
      (numberFieldAdeleLevelOver L (numberFieldExceptionalPreimage (L := L) S) (upperLevel K L S T)))
    (q : OriginalPlace L) :
    (x.changeRing (upperTransition K L S T U hTU)).changeRing
        (fieldProjection L (numberFieldExceptionalPreimage (L := L) S) (upperLevel K L S U) q) =
      x.changeRing
        (fieldProjection L (numberFieldExceptionalPreimage (L := L) S) (upperLevel K L S T) q) := by
  apply RingPoint.ext
  change Spec.map _ ≫ (Spec.map _ ≫ x.left) = Spec.map _ ≫ x.left
  rw [← Category.assoc, ← Spec.map_comp]
  cases q <;> rfl

omit [CompactSpace Y.left] [QuasiSeparatedSpace Y.left] in
/-- Canonical evaluation is independent of enlarging the lower support over the original integral base. -/
theorem fieldEvaluation_natural
    (p : RingPoint ((S : Set (FinitePlace K)).integer K) (affineChartWeilRestriction ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y) (numberFieldAdeleLevelOver K S T))
    (v : OriginalPlace K) (q : PlacesAbove K L v) :
    fieldEvaluation K L S U Y v q
        (p.changeRing (numberFieldAdeleLevelOverMap K S hTU).hom) =
      fieldEvaluation K L S T Y v q p :=
  weilRestrictionEvaluation_natural_lower ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) (numberFieldAdeleLevelOver K S T) (numberFieldAdeleLevelOver K S U)
    (OriginalCompletion L (upperPlace K L v q))
    (upperFieldCoefficient K L S T v q) (upperFieldCoefficient K L S U v q)
    (upperFieldCoefficient_compatible K L S T v q)
    (upperFieldCoefficient_compatible K L S U v q)
    (numberFieldAdeleLevelOverMap K S hTU).hom (by
      apply RingHom.ext
      intro a
      cases v <;> rfl) Y p

/-- The two original fixed-model Weil homeomorphisms commute with the two literal support inclusions. -/
theorem levelPoint_natural
    (p : RingPoint ((S : Set (FinitePlace K)).integer K) (affineChartWeilRestriction ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y) (numberFieldAdeleLevelOver K S T)) :
    NumberFieldSIntegerFixedLevelRegroup.adelicLevelPointHomeomorph K L S U Y n j hj
      (p.changeRing (numberFieldAdeleLevelOverMap K S hTU).hom) =
        (NumberFieldSIntegerFixedLevelRegroup.adelicLevelPointHomeomorph K L S T Y n j hj p).changeRing
          (upperTransition K L S T U hTU) := by
  let : IsSeparated Y.hom := isSeparated_of_projectiveImmersion (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y n j hj
  apply point_ext L (numberFieldExceptionalPreimage (L := L) S) (upperLevel K L S U) Y
  intro q₀
  cases q₀ with
  | inl q₀ =>
    let v : OriginalPlace K := .inl (q₀.comap (algebraMap K L))
    let q : PlacesAbove K L v := ⟨q₀, ⟨rfl⟩⟩
    exact (levelPoint_fieldEvaluation_at K L S U Y n j hj
        (p.changeRing (numberFieldAdeleLevelOverMap K S hTU).hom) v q).trans
      ((fieldEvaluation_natural K L S T Y U hTU p v q).trans
        ((levelPoint_fieldEvaluation_at K L S T Y n j hj p v q).symm.trans
          (upperTransition_pointField K L S T Y U hTU
            (NumberFieldSIntegerFixedLevelRegroup.adelicLevelPointHomeomorph K L S T Y n j hj p) (.inl q₀)).symm))
  | inr q₀ =>
    let v : OriginalPlace K := .inr (q₀.under (NumberField.RingOfIntegers K))
    let q : PlacesAbove K L v := ⟨q₀, inferInstance⟩
    exact (levelPoint_fieldEvaluation_at K L S U Y n j hj
        (p.changeRing (numberFieldAdeleLevelOverMap K S hTU).hom) v q).trans
      ((fieldEvaluation_natural K L S T Y U hTU p v q).trans
        ((levelPoint_fieldEvaluation_at K L S T Y n j hj p v q).symm.trans
          (upperTransition_pointField K L S T Y U hTU
            (NumberFieldSIntegerFixedLevelRegroup.adelicLevelPointHomeomorph K L S T Y n j hj p) (.inr q₀)).symm))


end Langlands.Global.NumberFieldFixedLevelWeilEvaluation

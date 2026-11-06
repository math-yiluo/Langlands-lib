import Langlands.Global.NumberFieldFixedModelWeilHomeomorph
import Langlands.Global.AdelicFunctoriality.Inclusion

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology IsDedekindDomain
open _root_.AlgebraicGeometry
open scoped NumberField NumberField.LiesOver
  Langlands.Global Langlands.Global.NumberFieldSIntegers
  Langlands.Global.AdelicFunctoriality.FiniteExtension

namespace Langlands.Global.NumberFieldFixedModelWeilEvaluation

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.PointTopology
open AdelicFunctoriality NumberFieldFixedLevelWeilEvaluation

set_option backward.isDefEq.respectTransparency false

section Projections

variable (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))

/-- The literal projection from full adeles to an original completed field. -/
def fullFieldProjection (v : OriginalPlace K) :
    numberFieldAdeleOver K S →ₐ[((S : Set (FinitePlace K)).integer K)]
      OriginalCompletion K v := by
  cases v with
  | inl v => exact { toRingHom := infiniteProjection K v, commutes' := fun _ => rfl }
  | inr v => exact { toRingHom := finiteProjection K v, commutes' := fun _ => rfl }

/-- All original completed-field projections of the full adele ring. -/
def fullFieldProduct : numberFieldAdeleOver K S →ₐ[((S : Set (FinitePlace K)).integer K)]
    ∀ v : OriginalPlace K, OriginalCompletion K v :=
  AlgHom.pi (fullFieldProjection K S)

/-- Original infinite and finite coordinates determine every full adele. -/
theorem fullFieldProduct_injective : Function.Injective (fullFieldProduct K S) := by
  intro a b h
  apply Prod.ext
  · funext v
    exact congrFun h (.inl v)
  · apply RestrictedProduct.ext
    intro v
    exact congrFun h (.inr v)

variable (Y : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
  [IsSeparated Y.hom] [QuasiSeparatedSpace Y.left]

/-- Original completed-field coordinates determine points of a separated model on full adeles. -/
theorem full_point_ext (p q : NumberFieldFixedModelAdelePoints K S Y)
    (h : ∀ v : OriginalPlace K, p.changeRing (fullFieldProjection K S v) =
      q.changeRing (fullFieldProjection K S v)) : p = q := by
  let : IsReduced (numberFieldAdeleOver K S) :=
    isReduced_of_injective (fullFieldProduct K S) (fullFieldProduct_injective K S)
  apply schemeSeparatedCoefficientInjectivity_proof ((S : Set (FinitePlace K)).integer K)
    (numberFieldAdeleOver K S) (∀ v : OriginalPlace K, OriginalCompletion K v) Y
    (fullFieldProduct K S) (fullFieldProduct_injective K S)
  apply productPointMap_injective ((S : Set (FinitePlace K)).integer K)
    (fun v : OriginalPlace K => OriginalCompletion K v) Y
  funext v
  apply RingPoint.ext
  change Spec.map _ ≫ (Spec.map _ ≫ p.left) = Spec.map _ ≫ (Spec.map _ ≫ q.left)
  rw [← Category.assoc, ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
  exact congrArg (fun x => x.left) (h v)

omit [IsSeparated Y.hom] [QuasiSeparatedSpace Y.left] in
/-- Inclusion of an arithmetic level preserves every original completed-field coordinate. -/
theorem stage_pointField (T : AdelicLevelIndexAbove S)
    (p : RingPoint ((S : Set (FinitePlace K)).integer K) Y (numberFieldAdeleLevelOver K S T))
    (v : OriginalPlace K) :
    (p.changeRing (numberFieldAdeleLevelOverι K S T).hom).changeRing
        (fullFieldProjection K S v) = p.changeRing (fieldProjection K S T v) := by
  apply RingPoint.ext
  change Spec.map _ ≫ (Spec.map _ ≫ p.left) = Spec.map _ ≫ p.left
  rw [← Category.assoc, ← Spec.map_comp]
  cases v <;> rfl

end Projections

variable (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] (S : Finset (FinitePlace K))

/-- The literal full adele inclusion retains the two original integral bases. -/
theorem adeleInclusion_compatible :
    (adeleInclusion (K := K) (L := L)).comp
        (algebraMap ((S : Set (FinitePlace K)).integer K) (numberFieldAdeleOver K S)) =
      (algebraMap (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) (numberFieldAdeleOver L (numberFieldExceptionalPreimage (L := L) S))).comp
        (algebraMap ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L)) := by
  apply RingHom.ext
  intro a
  exact adeleInclusion_diagonal (K := K) (L := L) a.val

/-- The original lower full adele evaluated in one original upper completed field. -/
def fullUpperFieldCoefficient (v : OriginalPlace K) (q : PlacesAbove K L v) :
    numberFieldAdeleOver K S →+* OriginalCompletion L (upperPlace K L v q) :=
  (completionCoefficient K L v q).comp (fullFieldProjection K S v).toRingHom

/-- Full adelic field evaluation preserves both original integral bases. -/
theorem fullUpperFieldCoefficient_compatible (v : OriginalPlace K) (q : PlacesAbove K L v) :
    (fullUpperFieldCoefficient K L S v q).comp (algebraMap ((S : Set (FinitePlace K)).integer K) (numberFieldAdeleOver K S)) =
      (algebraMap (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) (OriginalCompletion L (upperPlace K L v q))).comp
        (algebraMap ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L)) := by
  apply RingHom.ext
  intro a
  cases v with
  | inl v => exact completionCoefficient_algebraMap K L (.inl v) q a.val
  | inr v => exact completionCoefficient_algebraMap K L (.inr v) q a.val

/-- Evaluation in each upper completed field is the corresponding coordinate of the literal inclusion. -/
theorem fullUpperFieldCoefficient_eq_projection (v : OriginalPlace K) (q : PlacesAbove K L v) :
    fullUpperFieldCoefficient K L S v q =
      (fullFieldProjection L (numberFieldExceptionalPreimage (L := L) S)
        (upperPlace K L v q)).toRingHom.comp (adeleInclusion (K := K) (L := L)) := by
  apply RingHom.ext
  intro a
  cases v with
  | inl v =>
    rcases q with ⟨q, hq⟩
    let := hq
    change NumberField.LiesOver.completionMap (v := v) (w := q) (a.1 v) =
      infiniteCompletionMap (algebraMap K L) q (a.1 (q.comap (algebraMap K L)))
    have hv : q.comap (algebraMap K L) = v :=
      NumberField.InfinitePlace.LiesOver.comap_eq q v
    subst hv
    rfl
  | inr v =>
    rcases q with ⟨q, hq⟩
    let := hq
    change FiniteExtension.completionMap v q (a.2 v) =
      FiniteExtension.completionMap (q.under (NumberField.RingOfIntegers K)) q
        (a.2 (q.under (NumberField.RingOfIntegers K)))
    have hv : q.under (NumberField.RingOfIntegers K) = v :=
      HeightOneSpectrum.ext (q.asIdeal.over_def v.asIdeal).symm
    subst hv
    rfl

variable (Y : Over (Spec (CommRingCat.of (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L)))) [LocallyOfFiniteType Y.hom]

/-- The original integral Weil counit evaluated along the literal full adele inclusion. -/
def adelicEvaluation (p : NumberFieldFixedModelAdelePoints K S
    (affineChartWeilRestriction ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y)) :
    NumberFieldFixedModelAdelePoints L (numberFieldExceptionalPreimage (L := L) S) Y :=
  weilRestrictionEvaluation ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) (numberFieldAdeleOver K S)
    (numberFieldAdeleOver L (numberFieldExceptionalPreimage (L := L) S))
    (adeleInclusion (K := K) (L := L)) (adeleInclusion_compatible K L S) Y p

/-- The full counit's coordinate is evaluation of the original lower point in that completed field. -/
theorem adelicEvaluation_field (p : NumberFieldFixedModelAdelePoints K S
    (affineChartWeilRestriction ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y)) (v : OriginalPlace K) (q : PlacesAbove K L v) :
    (adelicEvaluation K L S Y p).changeRing
        (fullFieldProjection L (numberFieldExceptionalPreimage (L := L) S) (upperPlace K L v q)) =
      weilRestrictionEvaluation ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) (numberFieldAdeleOver K S)
        (OriginalCompletion L (upperPlace K L v q)) (fullUpperFieldCoefficient K L S v q)
        (fullUpperFieldCoefficient_compatible K L S v q) Y p := by
  exact weilRestrictionEvaluation_natural_upper ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) (numberFieldAdeleOver K S)
    (numberFieldAdeleOver L (numberFieldExceptionalPreimage (L := L) S))
    (OriginalCompletion L (upperPlace K L v q))
    (adeleInclusion (K := K) (L := L)) (fullUpperFieldCoefficient K L S v q)
    (adeleInclusion_compatible K L S) (fullUpperFieldCoefficient_compatible K L S v q)
    (fullFieldProjection L (numberFieldExceptionalPreimage (L := L) S) (upperPlace K L v q))
    (fullUpperFieldCoefficient_eq_projection K L S v q).symm Y p

/-- On a point from a level, each coordinate of full evaluation is the original level evaluation. -/
theorem adelicEvaluation_stage_field (T : AdelicLevelIndexAbove S)
    (p : RingPoint ((S : Set (FinitePlace K)).integer K) (affineChartWeilRestriction ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y) (numberFieldAdeleLevelOver K S T))
    (v : OriginalPlace K) (q : PlacesAbove K L v) :
    (adelicEvaluation K L S Y (p.changeRing (numberFieldAdeleLevelOverι K S T).hom)).changeRing
        (fullFieldProjection L (numberFieldExceptionalPreimage (L := L) S) (upperPlace K L v q)) =
      fieldEvaluation K L S T Y v q p := by
  rw [adelicEvaluation_field]
  exact weilRestrictionEvaluation_natural_lower ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) (numberFieldAdeleLevelOver K S T)
    (numberFieldAdeleOver K S) (OriginalCompletion L (upperPlace K L v q))
    (upperFieldCoefficient K L S T v q) (fullUpperFieldCoefficient K L S v q)
    (upperFieldCoefficient_compatible K L S T v q)
    (fullUpperFieldCoefficient_compatible K L S v q)
    (numberFieldAdeleLevelOverι K S T).hom (by
      apply RingHom.ext
      intro a
      cases v <;> rfl) Y p

variable [CompactSpace Y.left] (n : ℕ)
  (j : Y.left ⟶ ProjectiveSpace (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) n) [IsImmersion j]
  (hj : j ≫ projectiveSpaceToSpec (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) n = Y.hom)

/-- On every original arithmetic stage, the full homeomorphism is the actual integral counit. -/
theorem adelicPointHomeomorph_stage_eq_evaluation (T : AdelicLevelIndexAbove S)
    (p : RingPoint ((S : Set (FinitePlace K)).integer K) (affineChartWeilRestriction ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y)
      (numberFieldAdeleLevelOver K S T)) :
    NumberFieldFixedModelWeilHomeomorph.adelicPointHomeomorph K S L Y n j hj
        (p.changeRing (numberFieldAdeleLevelOverι K S T).hom) =
      adelicEvaluation K L S Y (p.changeRing (numberFieldAdeleLevelOverι K S T).hom) := by
  let : IsSeparated Y.hom := isSeparated_of_projectiveImmersion _ Y n j hj
  let : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  rw [NumberFieldFixedModelWeilHomeomorph.adelicPointHomeomorph_stage]
  apply full_point_ext L (numberFieldExceptionalPreimage (L := L) S) Y
  intro q₀
  cases q₀ with
  | inl q₀ =>
    let v : OriginalPlace K := .inl (q₀.comap (algebraMap K L))
    let q : PlacesAbove K L v := ⟨q₀, ⟨rfl⟩⟩
    exact (stage_pointField L (numberFieldExceptionalPreimage (L := L) S) Y
        (NumberFieldSIntegerFixedLevelRegroup.upperLevel K L S T)
        (NumberFieldSIntegerFixedLevelRegroup.adelicLevelPointHomeomorph K L S T Y n j hj p)
        (.inl q₀)).trans
      ((levelPoint_fieldEvaluation_at K L S T Y n j hj p v q).trans
        (adelicEvaluation_stage_field K L S Y T p v q).symm)
  | inr q₀ =>
    let v : OriginalPlace K := .inr (q₀.under (NumberField.RingOfIntegers K))
    let q : PlacesAbove K L v := ⟨q₀, inferInstance⟩
    exact (stage_pointField L (numberFieldExceptionalPreimage (L := L) S) Y
        (NumberFieldSIntegerFixedLevelRegroup.upperLevel K L S T)
        (NumberFieldSIntegerFixedLevelRegroup.adelicLevelPointHomeomorph K L S T Y n j hj p)
        (.inr q₀)).trans
      ((levelPoint_fieldEvaluation_at K L S T Y n j hj p v q).trans
        (adelicEvaluation_stage_field K L S Y T p v q).symm)

/-- The original fixed-model full adelic homeomorphism evaluates the original Weil counit
along the literal full adele inclusion. -/
theorem adelicPointHomeomorph_eq_evaluation
    (p : NumberFieldFixedModelAdelePoints K S (affineChartWeilRestriction ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y)) :
    NumberFieldFixedModelWeilHomeomorph.adelicPointHomeomorph K S L Y n j hj p =
      adelicEvaluation K L S Y p := by
  obtain ⟨T, q, rfl⟩ :=
    ((numberFieldFixedModelPointComparisonProperties K S
      (affineChartWeilRestriction ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y)).2 inferInstance).1 p
  exact adelicPointHomeomorph_stage_eq_evaluation K L S Y n j hj T q

end Langlands.Global.NumberFieldFixedModelWeilEvaluation

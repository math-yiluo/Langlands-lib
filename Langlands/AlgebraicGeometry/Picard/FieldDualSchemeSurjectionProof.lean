import Langlands.AlgebraicGeometry.Picard.FieldDualSchemeSurjectionStatement
import Langlands.AlgebraicGeometry.Modules.PullbackTensorProof
import Langlands.AlgebraicGeometry.Picard.MumfordMap
import Langlands.AlgebraicGeometry.Picard.MumfordBundlePicardZeroProof
import Langlands.AlgebraicGeometry.Picard.DualSchemeTensor
import Langlands.AlgebraicGeometry.Picard.PicardZeroPullbackProof
import Langlands.AbelianScheme.FieldAmpleExistenceProof
import Langlands.AlgebraicGeometry.Picard.FieldLineBundleTrivialityProof
import Langlands.AlgebraicGeometry.Picard.LineBundleDualEvaluation
import Langlands.AlgebraicGeometry.Picard.TranslationBaseChange
import Langlands.AlgebraicGeometry.Picard.GeometricPicardZeroInverse
import Langlands.AlgebraicGeometry.Picard.FieldMumfordPointComparisonProof
import Langlands.AlgebraicGeometry.Picard.FieldBaseChangeAmpleProof
import Langlands.AlgebraicGeometry.Picard.AlgClosedFieldTranslationDifferenceLiftingProof
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Surjectivity onto the chosen dual parameter scheme over every field -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

/-- Over a field, rigidification keeps the chosen ample bundle's actual carrier.
The inverse and its evaluation are constructed from that same bundle. -/
theorem exists_rigidified_ample_of_fieldAmpleExistence
    (existence : GroupScheme.FieldAmpleExistenceStatement.{u})
    (k : Type u) [Field k] (A : AbelianScheme (Spec (CommRingCat.of k))) :
    ∃ (L : RigidifiedLineBundle (unitSection A)) (M : LineBundle A.X.left)
      (_ : tensorObj L.obj.carrier M.obj ≅ structureSheaf A.X.left),
      ((RigidifiedLineBundle.forget (unitSection A)).obj L).IsAmple := by
  obtain ⟨L, hL⟩ := existence k A.toGrp A.smooth A.proper A.geometricallyConnected
  obtain ⟨e⟩ := fieldLineBundleTriviality k ((LineBundle.pullback (unitSection A)).obj L)
  obtain ⟨M, ⟨evaluation⟩⟩ := L.exists_tensorObj_iso_structureSheaf
  exact ⟨RigidifiedLineBundle.ofLineBundle L e.symm, M, evaluation, hL⟩

/-- A section of the actual base change yields a point over the original base. -/
theorem exists_point_of_baseChangeSection {S S' : Scheme.{u}} (A : AbelianScheme S)
    (b : S' ⟶ S) (x : Over.mk (𝟙 S') ⟶ ((baseChange b).obj A).X) :
    ∃ a : Over.mk b ⟶ A.X,
      x.left ≫ CategoryTheory.Limits.pullback.fst A.X.hom b = a.left := by
  refine ⟨Over.homMk (x.left ≫ CategoryTheory.Limits.pullback.fst A.X.hom b) ?_, rfl⟩
  change (x.left ≫ CategoryTheory.Limits.pullback.fst A.X.hom b) ≫ A.X.hom = b
  rw [Category.assoc, CategoryTheory.Limits.pullback.condition, ← Category.assoc]
  change (x.left ≫ ((baseChange b).obj A).X.hom) ≫ b = b
  rw [x.w]
  change (𝟙 S') ≫ b = b
  exact Category.id_comp b

/-- Every algebraically closed point of the chosen parameter scheme gives an
ordinary translation-invariant bundle on the actual changed abelian scheme. -/
theorem poincare_point_translation_invariant {S : Scheme.{u}} (A : AbelianScheme S)
    (hA : HasDualScheme A) (K : Type u) [Field K] [IsAlgClosed K]
    (b : Spec (CommRingCat.of K) ⟶ S) (p : Over.mk b ⟶ dualScheme A hA) :
    GroupScheme.IsTranslationInvariant ((baseChange b).obj A).toGrp
      (familyLineBundle (S := S) A (T := Over.mk b)
        ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
          (unitSection_comp A) (T := Over.mk b) (U := dualScheme A hA) p).obj
            (poincareFamily A hA))) := by
  apply isTranslationInvariant_of_isGeometricallyPicardZero K ((baseChange b).obj A)
  exact picardZeroPullback S A (Over.mk b) (dualScheme A hA) p (poincareFamily A hA)
    (poincareFamily_universal A hA).1

/-- Lifts of every algebraically closed field-valued point imply surjectivity.
The test field for an underlying point is an algebraic closure of its residue field. -/
theorem surjective_of_algClosed_point_lifting {S : Scheme.{u}} {X Y : Over S}
    (f : X ⟶ Y)
    (lifting : ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (b : Spec (CommRingCat.of K) ⟶ S) (p : Over.mk b ⟶ Y),
      ∃ a : Over.mk b ⟶ X, a ≫ f = p) :
    Surjective f.left := by
  constructor
  intro y
  let κ := Y.left.residueField y
  let Ω := AlgebraicClosure κ
  let g : Spec (CommRingCat.of Ω) ⟶ Y.left :=
    Spec.map (CommRingCat.ofHom (algebraMap κ Ω)) ≫ Y.left.fromSpecResidueField y
  let b := g ≫ Y.hom
  let p : Over.mk b ⟶ Y := Over.homMk g rfl
  obtain ⟨a, ha⟩ := lifting Ω b p
  refine ⟨a.left (IsLocalRing.closedPoint Ω), ?_⟩
  have h := congrArg (fun m : Over.mk b ⟶ Y ↦ m.left (IsLocalRing.closedPoint Ω)) ha
  change f.left (a.left (IsLocalRing.closedPoint Ω)) =
    Y.left.fromSpecResidueField y
      ((Spec.map (CommRingCat.ofHom (algebraMap κ Ω))) (IsLocalRing.closedPoint Ω)) at h
  rwa [Scheme.fromSpecResidueField_apply] at h

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
variable (square : MumfordBundlePicardZeroStatement.{u})
variable {S : Scheme.{u}} (A : AbelianScheme S)
variable (L : RigidifiedLineBundle (unitSection A)) (M : LineBundle A.X.left)
variable (evaluation : tensorObj L.obj.carrier M.obj ≅ structureSheaf A.X.left)
variable (hA : HasDualScheme A)

/-- An actual rigidified point comparison gives equality in the chosen parameter scheme. -/
theorem mumford_point_eq_of_iso {T : Over S} (a : T ⟶ A.X)
    (p : T ⟶ dualScheme A hA)
    (e :
      (RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
        (unitSection_comp A) a).obj (mumfordBundle A preservation L M evaluation) ≅
      (RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
        (unitSection_comp A) p).obj (poincareFamily A hA)) :
    a ≫ mumfordSchemeMap preservation square A L M evaluation hA = p := by
  apply dualPointClass_injective picardZeroPullback A hA T
  apply Subtype.ext
  change RigidifiedLineBundle.classifyingMap A.X.hom (unitSection A)
      (unitSection_comp A) (poincareFamily A hA) T
      (a ≫ mumfordSchemeMap preservation square A L M evaluation hA) =
    RigidifiedLineBundle.classifyingMap A.X.hom (unitSection A)
      (unitSection_comp A) (poincareFamily A hA) T p
  rw [mumfordSchemeMap_points]
  exact Quotient.sound ⟨e⟩

include preservation square in
/-- Reduction to actual rigidified Mumford lifts, with no change of the chosen dual. -/
theorem mumfordSchemeMap_surjective_of_rigidified_lifts
    (lifting : ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (b : Spec (CommRingCat.of K) ⟶ S) (p : Over.mk b ⟶ dualScheme A hA),
      ∃ a : Over.mk b ⟶ A.X,
        Nonempty (
          (RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
            (unitSection_comp A) a).obj (mumfordBundle A preservation L M evaluation) ≅
          (RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
            (unitSection_comp A) p).obj (poincareFamily A hA))) :
    Surjective (mumfordSchemeMap preservation square A L M evaluation hA).left := by
  apply surjective_of_algClosed_point_lifting
  intro K _ _ b p
  obtain ⟨a, ⟨e⟩⟩ := lifting K b p
  exact ⟨a, mumford_point_eq_of_iso preservation square A L M evaluation hA a p e⟩

end Langlands.AbelianScheme

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

/-- Every abelian scheme over a field surjects onto its chosen universal
geometric Picard-zero parameter scheme. -/
theorem fieldDualSchemeSurjection : FieldDualSchemeSurjectionStatement.{u} := by
  let existence : GroupScheme.FieldAmpleExistenceStatement.{u} :=
    GroupScheme.fieldAmpleExistence
  let preservation : pullbackTensorComparisonIsIsoStatement.{u} :=
    pullbackTensorComparisonIsIso
  let square : MumfordBundlePicardZeroStatement.{u} := mumfordBundlePicardZero
  let lifting : AlgClosedFieldTranslationDifferenceLiftingStatement.{u} :=
    algClosedFieldTranslationDifferenceLifting
  intro k _ A hA
  obtain ⟨L, M, evaluation, hL⟩ :=
    exists_rigidified_ample_of_fieldAmpleExistence existence k A
  refine ⟨mumfordSchemeMap preservation square A L M evaluation hA, ?_⟩
  apply mumfordSchemeMap_surjective_of_rigidified_lifts
    preservation square A L M evaluation hA
  intro K _ _ b p
  let i := CategoryTheory.Limits.pullback.fst A.X.hom b
  let L₀ := (RigidifiedLineBundle.forget (unitSection A)).obj L
  let LK : LineBundle ((baseChange b).obj A).X.left := (LineBundle.pullback i).obj L₀
  let MK : LineBundle ((baseChange b).obj A).X.left := (LineBundle.pullback i).obj M
  let Q : RigidifiedFamily A (Over.mk b) :=
    (RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
      (unitSection_comp A) (T := Over.mk b) (U := dualScheme A hA) p).obj
        (poincareFamily A hA)
  let P : LineBundle ((baseChange b).obj A).X.left :=
    familyLineBundle (S := Spec (CommRingCat.of k)) A (T := Over.mk b) Q
  have hLK : LK.IsAmple := fieldBaseChangeAmple k K b A.X.left A.X.hom L₀ hL
  let evaluationK : tensorObj LK.obj MK.obj ≅ structureSheaf ((baseChange b).obj A).X.left :=
    pullbackTensorEvaluation preservation i L₀.obj M.obj evaluation
  have hP : GroupScheme.IsTranslationInvariant ((baseChange b).obj A).toGrp P :=
    poincare_point_translation_invariant A hA K b p
  obtain ⟨x, hx⟩ :=
    lifting preservation K ((baseChange b).obj A) LK MK evaluationK P hLK hP
  obtain ⟨a, ha⟩ := exists_point_of_baseChangeSection A b x
  exact ⟨a, fieldMumfordPointComparison preservation k A L M evaluation K b a x ha Q hx⟩

end Langlands.AbelianScheme

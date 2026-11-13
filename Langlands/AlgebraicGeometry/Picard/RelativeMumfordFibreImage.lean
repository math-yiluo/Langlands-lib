import Langlands.AlgebraicGeometry.Picard.FieldDualSchemeSurjectionProof
import Langlands.AlgebraicGeometry.Picard.FibreAmplenessBaseChange
import Langlands.AlgebraicGeometry.Picard.MumfordLineBundle
import Langlands.AlgebraicGeometry.Picard.LineBundleIsoLemmas
import Langlands.AlgebraicGeometry.Picard.AmpleIsoProof

/-! # Mumford maps hit every dual point over the ample-fibre locus -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

/-- The rigidified Mumford comparison at a field-valued point over an arbitrary base. -/
theorem relativeMumfordPointComparison
    (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    {S : Scheme.{u}} (A : AbelianScheme S)
    (L : RigidifiedLineBundle (unitSection A)) (M : LineBundle A.X.left)
    (evaluation : tensorObj L.obj.carrier M.obj ≅ structureSheaf A.X.left)
    (K : Type u) [Field K] (b : Spec (CommRingCat.of K) ⟶ S)
    (a : Over.mk b ⟶ A.X)
    (x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ ((baseChange b).obj A).X)
    (hx : x.left ≫ pullback.fst A.X.hom b = a.left)
    (Q : RigidifiedFamily A (Over.mk b))
    (premise : Nonempty (LineBundle.tensor preservation
          ((LineBundle.pullback
            (GroupScheme.translation ((baseChange b).obj A).toGrp x).left).obj
              ((LineBundle.pullback (pullback.fst A.X.hom b)).obj
                ((RigidifiedLineBundle.forget (unitSection A)).obj L)))
          ((LineBundle.pullback (pullback.fst A.X.hom b)).obj M) ≅
        familyLineBundle A (T := Over.mk b) Q)) :
    Nonempty ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
          (unitSection_comp A) (T := Over.mk b) a).obj
            (mumfordBundle A preservation L M evaluation) ≅ Q) := by
  obtain ⟨premise⟩ := premise
  exact ⟨RigidifiedLineBundle.isoOfCarrierIso preservation
    ((relativeProjection A.X.hom).app (Over.mk b))
    (relativeSection_projection _ _ _ _)
    (FieldMumfordPoint.carrierIso A a preservation x hx L.obj.carrier M.obj Q.obj.carrier
      (fieldLineBundleTriviality K ((LineBundle.pullback a.left).obj M)).some
      ((LineBundle.forget _).mapIso premise))⟩

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
variable (square : MumfordBundlePicardZeroStatement.{u})

/-- Over an arbitrary base, an algebraically closed point of the chosen dual lifts
through the Mumford map whenever the bundle is ample on the corresponding fibre. -/
theorem relativeMumfordLift {S : Scheme.{u}} (A : AbelianScheme S)
    (L : RigidifiedLineBundle (unitSection A)) (M : LineBundle A.X.left)
    (evaluation : tensorObj L.obj.carrier M.obj ≅ structureSheaf A.X.left)
    (hA : HasDualScheme A)
    (K : Type u) [Field K] [IsAlgClosed K] (b : Spec (CommRingCat.of K) ⟶ S)
    (p : Over.mk b ⟶ dualScheme A hA)
    (hLK : ((LineBundle.pullback (pullback.fst A.X.hom b)).obj
      ((RigidifiedLineBundle.forget (unitSection A)).obj L)).IsAmple) :
    ∃ a : Over.mk b ⟶ A.X, a ≫ mumfordSchemeMap preservation square A L M evaluation hA = p := by
  let lifting : AlgClosedFieldTranslationDifferenceLiftingStatement.{u} :=
    algClosedFieldTranslationDifferenceLifting
  let i := pullback.fst A.X.hom b
  let L₀ := (RigidifiedLineBundle.forget (unitSection A)).obj L
  let LK : LineBundle ((baseChange b).obj A).X.left := (LineBundle.pullback i).obj L₀
  let MK : LineBundle ((baseChange b).obj A).X.left := (LineBundle.pullback i).obj M
  let Q : RigidifiedFamily A (Over.mk b) :=
    (RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
      (unitSection_comp A) (T := Over.mk b) (U := dualScheme A hA) p).obj
        (poincareFamily A hA)
  let P : LineBundle ((baseChange b).obj A).X.left :=
    familyLineBundle (S := S) A (T := Over.mk b) Q
  let evaluationK : tensorObj LK.obj MK.obj ≅ structureSheaf ((baseChange b).obj A).X.left :=
    pullbackTensorEvaluation preservation i L₀.obj M.obj evaluation
  have hP : GroupScheme.IsTranslationInvariant ((baseChange b).obj A).toGrp P :=
    poincare_point_translation_invariant A hA K b p
  obtain ⟨x, hx⟩ :=
    lifting preservation K ((baseChange b).obj A) LK MK evaluationK P hLK hP
  obtain ⟨a, ha⟩ := exists_point_of_baseChangeSection A b x
  obtain ⟨e⟩ := relativeMumfordPointComparison preservation A L M evaluation K b a x ha Q hx
  exact ⟨a, mumford_point_eq_of_iso preservation square A L M evaluation hA a p e⟩

/-- Ampleness on the fibre at the image of a field point gives ampleness after pulling
back along that field point. -/
theorem isAmple_pullback_of_mem_ampleFibreLocus {X S : Scheme.{u}} (f : X ⟶ S)
    (L : LineBundle X) (K : Type u) [Field K] (b : Spec (CommRingCat.of K) ⟶ S)
    (hb : b (IsLocalRing.closedPoint K) ∈ ampleFibreLocus f L) :
    ((LineBundle.pullback (pullback.fst f b)).obj L).IsAmple := by
  have h1 := (mem_ampleFibreLocus_iff_of_isPullback (IsPullback.of_hasPullback f b) L
    (IsLocalRing.closedPoint K)).mpr hb
  exact (isAmple_pullback_iff_of_field_isPullback
    (IsPullback.of_hasPullback (pullback.snd f b)
      ((Spec (CommRingCat.of K)).fromSpecResidueField (IsLocalRing.closedPoint K))) _).mp h1

/-- Over a field point, twisting by a bundle pulled back from the base does not change
ampleness. -/
theorem isAmple_pullback_tensor_base {X S : Scheme.{u}} (f : X ⟶ S)
    (L : LineBundle X) (B : LineBundle S) (K : Type u) [Field K]
    (b : Spec (CommRingCat.of K) ⟶ S)
    (hL : ((LineBundle.pullback (pullback.fst f b)).obj L).IsAmple) :
    ((LineBundle.pullback (pullback.fst f b)).obj
      (LineBundle.tensor preservation L ((LineBundle.pullback f).obj B))).IsAmple := by
  obtain ⟨e⟩ := fieldLineBundleTriviality K ((LineBundle.pullback b).obj B)
  let e' : (LineBundle.pullback b).obj B ≅ LineBundle.trivial _ := ObjectProperty.isoMk _ e
  let E : (LineBundle.pullback (pullback.fst f b)).obj
      (LineBundle.tensor preservation L ((LineBundle.pullback f).obj B)) ≅
        (LineBundle.pullback (pullback.fst f b)).obj L :=
    LineBundle.pullbackTensorObjIso preservation (pullback.fst f b) L _ ≪≫
      LineBundle.tensorIsoTrivialIso preservation _
        (LineBundle.pullbackCompEqIso (pullback.fst f b) f pullback.condition B ≪≫
          (LineBundle.pullbackCompEqIso (pullback.snd f b) b rfl B).symm ≪≫
          (LineBundle.pullback (pullback.snd f b)).mapIso e' ≪≫
          LineBundle.pullbackTrivialIso _)
  exact hL.of_iso ((LineBundle.forget _).mapIso E.symm)

/-- Every point of the chosen dual lying over the ample-fibre locus of the bundle
underlying the rigidified bundle `L` is in the image of its Mumford map. -/
theorem mem_range_mumfordSchemeMap {S : Scheme.{u}} (A : AbelianScheme S)
    (L : RigidifiedLineBundle (unitSection A)) (M : LineBundle A.X.left)
    (evaluation : tensorObj L.obj.carrier M.obj ≅ structureSheaf A.X.left)
    (hA : HasDualScheme A) (y : (dualScheme A hA).left)
    (hy : (dualScheme A hA).hom y ∈
      ampleFibreLocus A.X.hom ((RigidifiedLineBundle.forget (unitSection A)).obj L)) :
    y ∈ Set.range (mumfordSchemeMap preservation square A L M evaluation hA).left := by
  let Y := dualScheme A hA
  let κ := Y.left.residueField y
  let Ω := AlgebraicClosure κ
  let g : Spec (CommRingCat.of Ω) ⟶ Y.left :=
    Spec.map (CommRingCat.ofHom (algebraMap κ Ω)) ≫ Y.left.fromSpecResidueField y
  let b := g ≫ Y.hom
  let p : Over.mk b ⟶ Y := Over.homMk g rfl
  have hg : g (IsLocalRing.closedPoint Ω) = y := by
    change Y.left.fromSpecResidueField y
      ((Spec.map (CommRingCat.ofHom (algebraMap κ Ω))) (IsLocalRing.closedPoint Ω)) = y
    rw [Scheme.fromSpecResidueField_apply]
  have hb : b (IsLocalRing.closedPoint Ω) ∈
      ampleFibreLocus A.X.hom ((RigidifiedLineBundle.forget (unitSection A)).obj L) := by
    change Y.hom (g (IsLocalRing.closedPoint Ω)) ∈ _
    rwa [hg]
  obtain ⟨a, ha⟩ := relativeMumfordLift preservation square A L M evaluation hA Ω b p
    (isAmple_pullback_of_mem_ampleFibreLocus A.X.hom _ Ω b hb)
  refine ⟨a.left (IsLocalRing.closedPoint Ω), ?_⟩
  have h := congrArg (fun m : Over.mk b ⟶ Y ↦ m.left (IsLocalRing.closedPoint Ω)) ha
  simp only [Over.comp_left, Scheme.Hom.comp_apply] at h
  rw [h]
  exact hg

/-- The same for the Mumford map of an ordinary line bundle, normalized along the unit. -/
theorem mem_range_mumfordSchemeMapOfLineBundle {S : Scheme.{u}} (A : AbelianScheme S)
    (L : LineBundle A.X.left) (B : LineBundle S)
    (evaluationB :
      tensorObj ((Scheme.Modules.pullback (unitSection A)).obj L.obj) B.obj ≅ structureSheaf S)
    (M : LineBundle A.X.left)
    (evaluation : tensorObj
      (LineBundle.normalize preservation A.X.hom (unitSection A) (unitSection_comp A)
        L B evaluationB).obj.carrier M.obj ≅ structureSheaf A.X.left)
    (hA : HasDualScheme A) (y : (dualScheme A hA).left)
    (hy : (dualScheme A hA).hom y ∈ ampleFibreLocus A.X.hom L) :
    y ∈ Set.range
      (mumfordSchemeMapOfLineBundle preservation A L B evaluationB M evaluation square hA).left := by
  let Y := dualScheme A hA
  let κ := Y.left.residueField y
  let Ω := AlgebraicClosure κ
  let g : Spec (CommRingCat.of Ω) ⟶ Y.left :=
    Spec.map (CommRingCat.ofHom (algebraMap κ Ω)) ≫ Y.left.fromSpecResidueField y
  let b := g ≫ Y.hom
  let p : Over.mk b ⟶ Y := Over.homMk g rfl
  have hg : g (IsLocalRing.closedPoint Ω) = y := by
    change Y.left.fromSpecResidueField y
      ((Spec.map (CommRingCat.ofHom (algebraMap κ Ω))) (IsLocalRing.closedPoint Ω)) = y
    rw [Scheme.fromSpecResidueField_apply]
  have hb : b (IsLocalRing.closedPoint Ω) ∈ ampleFibreLocus A.X.hom L := by
    change Y.hom (g (IsLocalRing.closedPoint Ω)) ∈ _
    rwa [hg]
  obtain ⟨a, ha⟩ := relativeMumfordLift preservation square A
    (LineBundle.normalize preservation A.X.hom (unitSection A) (unitSection_comp A)
      L B evaluationB) M evaluation hA Ω b p
    (isAmple_pullback_tensor_base preservation A.X.hom L B Ω b
      (isAmple_pullback_of_mem_ampleFibreLocus A.X.hom L Ω b hb))
  refine ⟨a.left (IsLocalRing.closedPoint Ω), ?_⟩
  have h := congrArg (fun m : Over.mk b ⟶ Y ↦ m.left (IsLocalRing.closedPoint Ω)) ha
  simp only [Over.comp_left, Scheme.Hom.comp_apply] at h
  change (mumfordSchemeMap preservation square A _ M evaluation hA).left
    (a.left (IsLocalRing.closedPoint Ω)) = y
  rw [h]
  exact hg

end Langlands.AbelianScheme

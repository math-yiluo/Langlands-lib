import Langlands.AlgebraicGeometry.Picard.LineBundleIsoClassGroup
import Langlands.AlgebraicGeometry.Picard.PoincareSliceSymmetry
import Langlands.AlgebraicGeometry.Picard.PolarizationDiagonalMumfordStatement
import Langlands.AlgebraicGeometry.Picard.PicardZeroLineBundleClassificationProof
import Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof

/-! # Classes of Poincaré pullbacks at points -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.Picard.LineBundle (IsoClasses isoClass pullbackHom)

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
variable {S : Scheme.{u}} (A : AbelianScheme S)

lemma pairOver_left_relativeSpace_map {Z T U : Over S} (z : Z ⟶ T) (h : T ⟶ U)
    (x : Z ⟶ A.X) :
    (pairOver A z x).left ≫ (relativeSpace A.X.hom).map h = (pairOver A (z ≫ h) x).left := by
  apply pullback.hom_ext
  · rw [Category.assoc, relativeSpace_map_fst, pairOver_left, pairOver_left,
      pullback.lift_fst_assoc, pullback.lift_fst, Over.comp_left]
  · rw [Category.assoc, relativeSpace_map_snd, pairOver_left, pairOver_left,
      pullback.lift_snd, pullback.lift_snd]

lemma comp_pairOver_left {Z' Z T : Over S} (h : Z' ⟶ Z) (z : Z ⟶ T) (x : Z ⟶ A.X) :
    h.left ≫ (pairOver A z x).left = (pairOver A (h ≫ z) (h ≫ x)).left := by
  rw [pairOver_left, pairOver_left]
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Over.comp_left]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Over.comp_left]

/-- The isomorphism class of a pulled-back line bundle is the pullback of its class. -/
lemma isoClass_pullback_eq {X Y W : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ W) {h : X ⟶ W}
    (w : f ≫ g = h) (L : LineBundle W) :
    isoClass preservation ((LineBundle.pullback h).obj L) =
      pullbackHom preservation f (isoClass preservation ((LineBundle.pullback g).obj L)) := by
  rw [LineBundle.pullbackHom_isoClass]
  exact LineBundle.isoClass_eq_of_iso ((LineBundle.pullbackComp f g).app L ≪≫
    eqToIso (by rw [w])).symm

/-- The class at the point `(z, x)` of a family `L` on `T ×_S A`. -/
def familyPointClass {T Z : Over S} (L : RigidifiedFamily A T) (z : Z ⟶ T) (x : Z ⟶ A.X) :
    IsoClasses preservation Z.left :=
  isoClass preservation ((LineBundle.pullback (pairOver A z x).left).obj
    ((RigidifiedLineBundle.forget _).obj L))

lemma familyPointClass_comp {T Z Z' : Over S} (L : RigidifiedFamily A T) (h : Z' ⟶ Z)
    (z : Z ⟶ T) (x : Z ⟶ A.X) :
    familyPointClass preservation A L (h ≫ z) (h ≫ x) =
      pullbackHom preservation h.left (familyPointClass preservation A L z x) :=
  isoClass_pullback_eq preservation _ _ (comp_pairOver_left A h z x) _

lemma familyPointClass_relativePullback {T U Z : Over S} (L : RigidifiedFamily A U)
    (h : T ⟶ U) (z : Z ⟶ T) (x : Z ⟶ A.X) :
    familyPointClass preservation A
        ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A) (unitSection_comp A)
          h).obj L) z x =
      familyPointClass preservation A L (z ≫ h) x :=
  (isoClass_pullback_eq preservation (pairOver A z x).left ((relativeSpace A.X.hom).map h)
    (pairOver_left_relativeSpace_map A z h x) ((RigidifiedLineBundle.forget _).obj L)).symm

lemma familyPointClass_tensor {T Z : Over S} (L M : RigidifiedFamily A T) (z : Z ⟶ T)
    (x : Z ⟶ A.X) :
    familyPointClass preservation A (RigidifiedLineBundle.tensor preservation L M) z x =
      familyPointClass preservation A L z x * familyPointClass preservation A M z x :=
  LineBundle.isoClass_eq_of_iso (LineBundle.pullbackTensorObjIso preservation
    (pairOver A z x).left ((RigidifiedLineBundle.forget _).obj L)
    ((RigidifiedLineBundle.forget _).obj M))

lemma familyPointClass_congr {T Z : Over S} (L : RigidifiedFamily A T) {z z' : Z ⟶ T}
    (hz : z = z') {x x' : Z ⟶ A.X} (hx : x = x') :
    familyPointClass preservation A L z x = familyPointClass preservation A L z' x' := by
  subst hz hx
  rfl

lemma familyPointClass_eq_of_iso {T Z : Over S} {L M : RigidifiedFamily A T} (e : L ≅ M)
    (z : Z ⟶ T) (x : Z ⟶ A.X) :
    familyPointClass preservation A L z x = familyPointClass preservation A M z x :=
  LineBundle.isoClass_eq_of_iso
    ((LineBundle.pullback _).mapIso ((RigidifiedLineBundle.forget _).mapIso e))

lemma pairOver_relativeFst_relativeSnd_left (T : Over S) :
    (pairOver A (relativeFst A T) (relativeSnd A T)).left = 𝟙 _ := by
  rw [pairOver_left]
  apply pullback.hom_ext
  · rw [pullback.lift_fst, Category.id_comp, relativeFst_left]
  · rw [pullback.lift_snd, Category.id_comp, relativeSnd_left]

/-- The class of a family is its class at the tautological point. -/
lemma isoClass_forget_eq_familyPointClass {T : Over S} (L : RigidifiedFamily A T) :
    isoClass preservation ((RigidifiedLineBundle.forget _).obj L) =
      familyPointClass preservation A L (relativeFst A T) (relativeSnd A T) := by
  unfold familyPointClass
  rw [pairOver_relativeFst_relativeSnd_left]
  exact LineBundle.isoClass_eq_of_iso ((LineBundle.pullbackId _).app _).symm

lemma comp_relativeDiagonal {Z : Over S} (x : Z ⟶ A.X) :
    x.left ≫ relativeDiagonal A = (pairOver A x x).left := by
  rw [pairOver_left, relativeDiagonal]
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.comp_id]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.comp_id]

lemma pairOver_comp_mumfordFirst {Z : Over S} (u v : Z ⟶ A.X) :
    pairOver A u v ≫ mumfordFirst A = u := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, pairOver_left]
  exact pullback.lift_fst _ _ _

lemma pairOver_comp_mumfordSecond {Z : Over S} (u v : Z ⟶ A.X) :
    pairOver A u v ≫ mumfordSecond A = v := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, pairOver_left]
  exact pullback.lift_snd _ _ _

lemma pairOver_left_mumfordAddition {Z : Over S} (u v : Z ⟶ A.X) :
    (pairOver A u v).left ≫ mumfordAddition A = (u * v).left := by
  rw [mumfordAddition, ← Over.comp_left, MonObj.comp_mul, pairOver_comp_mumfordFirst,
    pairOver_comp_mumfordSecond]

lemma isoClass_pullback_tensor {X Y : Scheme.{u}} (g : X ⟶ Y) (L M : LineBundle Y) :
    isoClass preservation ((LineBundle.pullback g).obj (LineBundle.tensor preservation L M)) =
      isoClass preservation ((LineBundle.pullback g).obj L) *
        isoClass preservation ((LineBundle.pullback g).obj M) :=
  (LineBundle.isoClass_eq_of_iso (LineBundle.pullbackTensorObjIso preservation g L M)).trans
    (LineBundle.isoClass_tensor preservation _ _)

lemma isoClass_pullback_pullback {X Y W : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ W) {h : X ⟶ W}
    (w : f ≫ g = h) (L : LineBundle W) :
    isoClass preservation ((LineBundle.pullback f).obj ((LineBundle.pullback g).obj L)) =
      isoClass preservation ((LineBundle.pullback h).obj L) :=
  (isoClass_pullback_eq preservation f g w L).symm

section Mumford

variable (L : LineBundle A.X.left) (B : LineBundle S)
variable (evaluationB :
  tensorObj ((Scheme.Modules.pullback (unitSection A)).obj L.obj) B.obj ≅ structureSheaf S)
variable (M : LineBundle A.X.left)
variable (evaluation :
  tensorObj (LineBundle.normalize preservation A.X.hom (unitSection A)
    (unitSection_comp A) L B evaluationB).obj.carrier M.obj ≅ structureSheaf A.X.left)

/-- The class of the Mumford family of `L` at `(u, v)`:
`[(u v)^* (L ⊗ π^* B)] [u^* M] [v^* M]`. -/
lemma familyPointClass_mumfordFamily {Z : Over S} (u v : Z ⟶ A.X) :
    familyPointClass preservation A
        (mumfordFamilyOfLineBundle preservation A L B evaluationB M evaluation) u v =
      isoClass preservation ((LineBundle.pullback (u * v).left).obj
          (LineBundle.tensor preservation L ((LineBundle.pullback A.X.hom).obj B))) *
        isoClass preservation ((LineBundle.pullback u.left).obj M) *
        isoClass preservation ((LineBundle.pullback v.left).obj M) := by
  unfold familyPointClass
  rw [mumfordFamilyOfLineBundle_forget, isoClass_pullback_tensor, isoClass_pullback_tensor,
    isoClass_pullback_pullback preservation _ _ (pairOver_left_mumfordAddition A u v),
    isoClass_pullback_pullback preservation (pairOver A u v).left (pullback.fst A.X.hom A.X.hom)
      (h := u.left) (by rw [pairOver_left, pullback.lift_fst]),
    isoClass_pullback_pullback preservation (pairOver A u v).left (pullback.snd A.X.hom A.X.hom)
      (h := v.left) (by rw [pairOver_left, pullback.lift_snd])]

variable (square : MumfordBundlePicardZeroStatement.{u}) (hA : HasDualScheme A)

/-- The Poincaré classes along a Mumford map are symmetric. -/
lemma familyPointClass_mumfordSchemeMap_comm {Z : Over S} (u v : Z ⟶ A.X) :
    familyPointClass preservation A (poincareFamily A hA)
        (u ≫ mumfordSchemeMapOfLineBundle preservation A L B evaluationB M evaluation square hA)
        v =
      familyPointClass preservation A (poincareFamily A hA)
        (v ≫ mumfordSchemeMapOfLineBundle preservation A L B evaluationB M evaluation square hA)
        u := by
  rw [← familyPointClass_relativePullback, ← familyPointClass_relativePullback,
    familyPointClass_eq_of_iso preservation A
      (mumfordSchemeMapOfLineBundlePullbackIso preservation A L B evaluationB M evaluation
        square hA) u v,
    familyPointClass_eq_of_iso preservation A
      (mumfordSchemeMapOfLineBundlePullbackIso preservation A L B evaluationB M evaluation
        square hA) v u,
    familyPointClass_mumfordFamily, familyPointClass_mumfordFamily, mul_comm u v,
    mul_right_comm]

/-- A Mumford map has symmetric Poincaré slices at every point. -/
lemma poincareSliceSymmetric_mumfordSchemeMap {T : Over S} (t : T ⟶ A.X) :
    PoincareSliceSymmetric A hA
      (mumfordSchemeMapOfLineBundle preservation A L B evaluationB M evaluation square hA) t := by
  have h := familyPointClass_mumfordSchemeMap_comm preservation A L B evaluationB M evaluation
    square hA (relativeFst A T ≫ t) (relativeSnd A T)
  rw [Category.assoc] at h
  exact LineBundle.isoClass_eq_iff.mp h

end Mumford

end Langlands.AbelianScheme

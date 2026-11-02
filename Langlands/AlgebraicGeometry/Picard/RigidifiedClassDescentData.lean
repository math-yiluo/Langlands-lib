import Langlands.AlgebraicGeometry.Picard.RelativePointLifts
import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesZariskiSeparatedProof
import Langlands.AlgebraicGeometry.Modules.PullbackTransport

/-! # Descent comparisons from compatible rigidified classes -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle.ClassDescent

open Langlands.Scheme.Modules Langlands.SchemeModule

variable {S X : Scheme.{u}} (f : X ⟶ S) (ε : S ⟶ X)
  (section_eq : ε ≫ f = 𝟙 S) {T U : Over S} (h : U ⟶ T)
  (L : relative f ε section_eq U)
  (compat : ∀ (W : Over S) (a b : W ⟶ U), a ≫ h = b ≫ h →
    Nonempty ((relativePullback f ε section_eq a).obj L ≅
      (relativePullback f ε section_eq b).obj L))

/-- A chosen rigidified comparison supplied by compatibility of the local class. -/
def compatibleIso {W : Over S} (a b : W ⟶ U) (hab : a ≫ h = b ≫ h) :
    (relativePullback f ε section_eq a).obj L ≅
      (relativePullback f ε section_eq b).obj L :=
  Classical.choice (compat W a b hab)

/-- Uniqueness supplies the cocycle law before passing to ordinary modules. -/
lemma compatibleIso_comp
    (unique : ∀ (W : Over S) (M N : relative f ε section_eq W), Subsingleton (M ≅ N))
    {W : Over S} (a b c : W ⟶ U)
    (hab : a ≫ h = b ≫ h) (hbc : b ≫ h = c ≫ h) (hac : a ≫ h = c ≫ h) :
    (compatibleIso f ε section_eq h L compat a b hab).hom.hom.val ≫
        (compatibleIso f ε section_eq h L compat b c hbc).hom.hom.val =
      (compatibleIso f ε section_eq h L compat a c hac).hom.hom.val := by
  have he := (unique W _ _).elim
    (compatibleIso f ε section_eq h L compat a b hab ≪≫
      compatibleIso f ε section_eq h L compat b c hbc)
    (compatibleIso f ε section_eq h L compat a c hac)
  exact congrArg (fun e ↦ e.hom.hom.val) he

/-- Chosen comparisons commute with relative pullback, by uniqueness. -/
lemma compatibleIso_precomp
    (unique : ∀ (W : Over S) (M N : relative f ε section_eq W), Subsingleton (M ≅ N))
    {W W' : Over S} (g : W' ⟶ W) (a b : W ⟶ U) (a' b' : W' ⟶ U)
    (ha : g ≫ a = a') (hb : g ≫ b = b')
    (hab : a ≫ h = b ≫ h) (hab' : a' ≫ h = b' ≫ h) :
    (compatibleIso f ε section_eq h L compat a' b' hab').hom.hom.val =
      Langlands.Scheme.Modules.transport (C := L.obj.carrier) (D := L.obj.carrier)
        ((relativeSpace f).map g)
        (((relativeSpace f).map_comp g a).symm.trans (congrArg (relativeSpace f).map ha))
        (((relativeSpace f).map_comp g b).symm.trans (congrArg (relativeSpace f).map hb))
        (compatibleIso f ε section_eq h L compat a b hab).hom.hom.val := by
  let Ca := relativePullbackCompTo f ε section_eq a g a' ha
  let Cb := relativePullbackCompTo f ε section_eq b g b' hb
  let e := (Ca.app L).symm ≪≫
    (relativePullback f ε section_eq g).mapIso
      (compatibleIso f ε section_eq h L compat a b hab) ≪≫ Cb.app L
  have he : e = compatibleIso f ε section_eq h L compat a' b' hab' :=
    (unique W' _ _).elim _ _
  have hi : (relativePullback f ε section_eq g).map
        (compatibleIso f ε section_eq h L compat a b hab).hom ≫ Cb.hom.app L =
      Ca.hom.app L ≫ (compatibleIso f ε section_eq h L compat a' b' hab').hom := by
    rw [← he]
    simp [e]
  have hv := congrArg (fun z ↦ z.hom.val) hi
  change (Scheme.Modules.pullback ((relativeSpace f).map g)).map
        (compatibleIso f ε section_eq h L compat a b hab).hom.hom.val ≫
      (Cb.hom.app L).hom.val =
    (Ca.hom.app L).hom.val ≫
      (compatibleIso f ε section_eq h L compat a' b' hab').hom.hom.val at hv
  have hCa : (Ca.hom.app L).hom.val =
      (compIso ((relativeSpace f).map g) ((relativeSpace f).map a)
        ((relativeSpace f).map a')
        (((relativeSpace f).map_comp g a).symm.trans (congrArg (relativeSpace f).map ha))
        L.obj.carrier).hom := by
    exact (relativePullbackCompTo_hom_val f ε section_eq a g a' ha L).trans
      (compIso_hom _ _ _ _ _).symm
  have hCb : (Cb.hom.app L).hom.val =
      (compIso ((relativeSpace f).map g) ((relativeSpace f).map b)
        ((relativeSpace f).map b')
        (((relativeSpace f).map_comp g b).symm.trans (congrArg (relativeSpace f).map hb))
        L.obj.carrier).hom := by
    exact (relativePullbackCompTo_hom_val f ε section_eq b g b' hb L).trans
      (compIso_hom _ _ _ _ _).symm
  rw [hCa, hCb] at hv
  rw [← cancel_epi (compIso ((relativeSpace f).map g) ((relativeSpace f).map a)
    ((relativeSpace f).map a')
    (((relativeSpace f).map_comp g a).symm.trans (congrArg (relativeSpace f).map ha))
    L.obj.carrier).hom]
  simp only [Langlands.Scheme.Modules.transport, Iso.hom_inv_id_assoc]
  exact hv.symm

/-- Comparison for two lifts of a common total-space map, obtained by pulling back
an actual rigidified isomorphism along the point section. -/
def thetaCommon {V : Scheme.{u}} (r : V ⟶ (relativeSpace f).obj T)
    (a b : V ⟶ (relativeSpace f).obj U)
    (ha : a ≫ (relativeSpace f).map h = r) (hb : b ≫ (relativeSpace f).map h = r) :
    (Scheme.Modules.pullback a).obj L.obj.carrier ≅
      (Scheme.Modules.pullback b).obj L.obj.carrier :=
  (compIso (relativePointSection f r)
      ((relativeSpace f).map (pointLift f h r a ha)) a
      (pointLift_section f h r a ha) L.obj.carrier).symm ≪≫
    (Scheme.Modules.pullback (relativePointSection f r)).mapIso
      ((forgetToRigidified _ ⋙ RigidifiedModule.forget _).mapIso
        (compatibleIso f ε section_eq h L compat
          (pointLift f h r a ha) (pointLift f h r b hb)
          (pointLift_comp f h r a b ha hb))) ≪≫
    compIso (relativePointSection f r)
      ((relativeSpace f).map (pointLift f h r b hb)) b
      (pointLift_section f h r b hb) L.obj.carrier

lemma thetaCommon_hom {V : Scheme.{u}} (r : V ⟶ (relativeSpace f).obj T)
    (a b : V ⟶ (relativeSpace f).obj U)
    (ha : a ≫ (relativeSpace f).map h = r) (hb : b ≫ (relativeSpace f).map h = r) :
    (thetaCommon f ε section_eq h L compat r a b ha hb).hom =
      Langlands.Scheme.Modules.transport (relativePointSection f r) (pointLift_section f h r a ha)
        (pointLift_section f h r b hb)
        (compatibleIso f ε section_eq h L compat
          (pointLift f h r a ha) (pointLift f h r b hb)
          (pointLift_comp f h r a b ha hb)).hom.hom.val := rfl

/-- The common-point comparisons satisfy the cocycle law. -/
lemma thetaCommon_comp
    (unique : ∀ (W : Over S) (M N : relative f ε section_eq W), Subsingleton (M ≅ N))
    {V : Scheme.{u}} (r : V ⟶ (relativeSpace f).obj T)
    (a b c : V ⟶ (relativeSpace f).obj U)
    (ha : a ≫ (relativeSpace f).map h = r) (hb : b ≫ (relativeSpace f).map h = r)
    (hc : c ≫ (relativeSpace f).map h = r) :
    (thetaCommon f ε section_eq h L compat r a b ha hb).hom ≫
        (thetaCommon f ε section_eq h L compat r b c hb hc).hom =
      (thetaCommon f ε section_eq h L compat r a c ha hc).hom := by
  simp only [thetaCommon_hom]
  rw [← Langlands.Scheme.Modules.transport_comp, compatibleIso_comp f ε section_eq h L compat unique]

/-- Common-point comparisons commute with arbitrary precomposition. -/
lemma thetaCommon_precomp
    (unique : ∀ (B : Over S) (M N : relative f ε section_eq B), Subsingleton (M ≅ N))
    {V W : Scheme.{u}} (k : W ⟶ V) (r : V ⟶ (relativeSpace f).obj T)
    (a b : V ⟶ (relativeSpace f).obj U)
    (ha : a ≫ (relativeSpace f).map h = r) (hb : b ≫ (relativeSpace f).map h = r)
    (hka : (k ≫ a) ≫ (relativeSpace f).map h = k ≫ r)
    (hkb : (k ≫ b) ≫ (relativeSpace f).map h = k ≫ r) :
    (thetaCommon f ε section_eq h L compat (k ≫ r) (k ≫ a) (k ≫ b) hka hkb).hom =
      Langlands.Scheme.Modules.transport k rfl rfl
        (thetaCommon f ε section_eq h L compat r a b ha hb).hom := by
  have he := compatibleIso_precomp f ε section_eq h L compat unique
    (pointBaseMap f k r) (pointLift f h r a ha) (pointLift f h r b hb)
    (pointLift f h (k ≫ r) (k ≫ a) hka) (pointLift f h (k ≫ r) (k ≫ b) hkb)
    (pointLift_precomp f h k r a ha hka) (pointLift_precomp f h k r b hb hkb)
    (pointLift_comp f h r a b ha hb)
    (pointLift_comp f h (k ≫ r) (k ≫ a) (k ≫ b) hka hkb)
  rw [thetaCommon_hom, he, thetaCommon_hom]
  rw [Langlands.Scheme.Modules.transport_transport_eq _ _ (pointSection_precomp f k r),
    Langlands.Scheme.Modules.transport_transport]
  all_goals simp only [Category.assoc, pointLift_section]

/-- Ordinary descent comparisons attached to a compatible rigidified class. -/
def theta (V : Scheme.{u}) (a b : V ⟶ (relativeSpace f).obj U)
    (hab : a ≫ (relativeSpace f).map h = b ≫ (relativeSpace f).map h) :
    (Scheme.Modules.pullback a).obj L.obj.carrier ≅
      (Scheme.Modules.pullback b).obj L.obj.carrier :=
  thetaCommon f ε section_eq h L compat (a ≫ (relativeSpace f).map h) a b rfl hab.symm

lemma theta_eq_common {V : Scheme.{u}} (r : V ⟶ (relativeSpace f).obj T)
    (a b : V ⟶ (relativeSpace f).obj U)
    (ha : a ≫ (relativeSpace f).map h = r) (hb : b ≫ (relativeSpace f).map h = r)
    (hab : a ≫ (relativeSpace f).map h = b ≫ (relativeSpace f).map h) :
    theta f ε section_eq h L compat V a b hab =
      thetaCommon f ε section_eq h L compat r a b ha hb := by
  subst r
  rfl

/-- The ordinary comparisons satisfy the full module descent cocycle law. -/
lemma theta_comp
    (unique : ∀ (W : Over S) (M N : relative f ε section_eq W), Subsingleton (M ≅ N))
    (V : Scheme.{u}) (a b c : V ⟶ (relativeSpace f).obj U)
    (hab : a ≫ (relativeSpace f).map h = b ≫ (relativeSpace f).map h)
    (hbc : b ≫ (relativeSpace f).map h = c ≫ (relativeSpace f).map h)
    (hac : a ≫ (relativeSpace f).map h = c ≫ (relativeSpace f).map h) :
    (theta f ε section_eq h L compat V a b hab).hom ≫
        (theta f ε section_eq h L compat V b c hbc).hom =
      (theta f ε section_eq h L compat V a c hac).hom := by
  rw [theta_eq_common f ε section_eq h L compat _ a b rfl hab.symm,
    theta_eq_common f ε section_eq h L compat _ b c hab.symm hac.symm,
    theta_eq_common f ε section_eq h L compat _ a c rfl hac.symm]
  exact thetaCommon_comp f ε section_eq h L compat unique _ a b c rfl hab.symm hac.symm

end Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle.ClassDescent

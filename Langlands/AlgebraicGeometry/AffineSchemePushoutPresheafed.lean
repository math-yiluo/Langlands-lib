import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Geometry.RingedSpace.PresheafedSpace
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite TopologicalSpace
open AlgebraicGeometry TopCat.Presheaf

universe u v

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry.AffineSchemePushout

theorem pushforwardEq_inv_app {S T : TopCat.{v}} {a b : S ⟶ T}
    (h : a = b) (F : S.Presheaf CommRingCat.{u}) (U) :
    (pushforwardEq h F).inv.app U = F.map (eqToHom (by subst h; rfl)) := by
  subst h
  simp [pushforwardEq]

instance presheafPushforward_preservesPullbacks {S T : TopCat.{v}} (a : S ⟶ T) :
    PreservesLimitsOfShape WalkingCospan (pushforward CommRingCat.{u} a) := by
  change PreservesLimitsOfShape WalkingCospan
    ((whiskeringLeft _ _ CommRingCat.{u}).obj (Opens.map a).op)
  infer_instance

section Criterion

variable {W X Y Z : PresheafedSpace.{u, u + 1, v} CommRingCat.{u}}
  {f : W ⟶ X} {g : W ⟶ Y} {i : X ⟶ Z} {j : Y ⟶ Z}
  (w : f ≫ i = g ≫ j)
  (hT : IsPushout f.base g.base i.base j.base)

def firstPresheafMap :
    i.base _* X.presheaf ⟶ (f.base ≫ i.base) _* W.presheaf :=
  (pushforward CommRingCat i.base).map f.c

def commonPresheafMap :
    j.base _* Y.presheaf ⟶ (f.base ≫ i.base) _* W.presheaf :=
  (pushforward CommRingCat j.base).map g.c ≫
    (pushforwardEq (congrArg PresheafedSpace.Hom.base w).symm W.presheaf).hom

variable (hS : IsPullback i.c j.c
  (firstPresheafMap (f := f) (i := i)) (commonPresheafMap w))

def presheafedPushoutBase (s : PushoutCocone f g) : Z.carrier ⟶ s.pt.carrier :=
  hT.desc s.inl.base s.inr.base (congrArg PresheafedSpace.Hom.base s.condition)

@[simp]
theorem presheafedPushoutBase_inl (s : PushoutCocone f g) :
    i.base ≫ presheafedPushoutBase hT s = s.inl.base :=
  hT.inl_desc _ _ _

@[simp]
theorem presheafedPushoutBase_inr (s : PushoutCocone f g) :
    j.base ≫ presheafedPushoutBase hT s = s.inr.base :=
  hT.inr_desc _ _ _

def presheafedPushoutFst (s : PushoutCocone f g) :
    s.pt.presheaf ⟶ (presheafedPushoutBase hT s) _* (i.base _* X.presheaf) :=
  s.inl.c ≫ (pushforwardEq (presheafedPushoutBase_inl hT s) X.presheaf).inv

def presheafedPushoutSnd (s : PushoutCocone f g) :
    s.pt.presheaf ⟶ (presheafedPushoutBase hT s) _* (j.base _* Y.presheaf) :=
  s.inr.c ≫ (pushforwardEq (presheafedPushoutBase_inr hT s) Y.presheaf).inv

theorem presheafedPushout_compatibility (s : PushoutCocone f g) :
    presheafedPushoutFst hT s ≫
        (pushforward CommRingCat (presheafedPushoutBase hT s)).map
          ((pushforward CommRingCat i.base).map f.c) =
      presheafedPushoutSnd hT s ≫
        (pushforward CommRingCat (presheafedPushoutBase hT s)).map
          (commonPresheafMap w) := by
  apply NatTrans.ext
  funext U
  simp only [presheafedPushoutFst, presheafedPushoutSnd, commonPresheafMap,
    TopCat.Presheaf.comp_app, pushforward_map_app', pushforwardEq_inv_app,
    pushforwardEq_hom_app, Category.assoc]
  erw [f.c.naturality, g.c.naturality_assoc]
  erw [← PresheafedSpace.comp_c_app_assoc, PresheafedSpace.congr_app s.condition U]
  simp
  simp only [← W.presheaf.map_comp]
  congr 3

def presheafedPushoutDesc (s : PushoutCocone f g) : Z ⟶ s.pt where
  base := presheafedPushoutBase hT s
  c := (hS.map (pushforward CommRingCat (presheafedPushoutBase hT s))).lift
    (presheafedPushoutFst hT s) (presheafedPushoutSnd hT s)
    (presheafedPushout_compatibility w hT s)

theorem presheafedPushoutDesc_inl (s : PushoutCocone f g) :
    i ≫ presheafedPushoutDesc w hT hS s = s.inl := by
  apply PresheafedSpace.ext _ _ (presheafedPushoutBase_inl hT s)
  change ((hS.map (pushforward CommRingCat (presheafedPushoutBase hT s))).lift
    (presheafedPushoutFst hT s) (presheafedPushoutSnd hT s)
    (presheafedPushout_compatibility w hT s) ≫
      (pushforward CommRingCat (presheafedPushoutBase hT s)).map i.c) ≫ _ = _
  rw [IsPullback.lift_fst]
  apply NatTrans.ext
  funext U
  simp [presheafedPushoutFst, pushforwardEq_inv_app, eqToHom_map]

theorem presheafedPushoutDesc_inr (s : PushoutCocone f g) :
    j ≫ presheafedPushoutDesc w hT hS s = s.inr := by
  apply PresheafedSpace.ext _ _ (presheafedPushoutBase_inr hT s)
  change ((hS.map (pushforward CommRingCat (presheafedPushoutBase hT s))).lift
    (presheafedPushoutFst hT s) (presheafedPushoutSnd hT s)
    (presheafedPushout_compatibility w hT s) ≫
      (pushforward CommRingCat (presheafedPushoutBase hT s)).map j.c) ≫ _ = _
  rw [IsPullback.lift_snd]
  apply NatTrans.ext
  funext U
  simp [presheafedPushoutSnd, pushforwardEq_inv_app, eqToHom_map]

include w hT hS in
theorem presheafedPushout_hom_ext {T : PresheafedSpace.{u, u + 1, v} CommRingCat.{u}}
    {m n : Z ⟶ T} (hm : i ≫ m = i ≫ n) (hn : j ≫ m = j ≫ n) : m = n := by
  rcases m with ⟨mb, mc⟩
  rcases n with ⟨nb, nc⟩
  have hb : mb = nb := hT.hom_ext (congrArg PresheafedSpace.Hom.base hm)
    (congrArg PresheafedSpace.Hom.base hn)
  subst nb
  suffices mc = nc by cases this; rfl
  apply (hS.map (pushforward CommRingCat mb)).hom_ext
  · apply NatTrans.ext
    funext U
    simpa using PresheafedSpace.congr_app hm U
  · apply NatTrans.ext
    funext U
    simpa using PresheafedSpace.congr_app hn U

/-- The colimit witness from a topological pushout and a pullback of pushed presheaves. -/
def presheafedPushoutIsColimit :
    IsColimit (PushoutCocone.mk i j w) := by
  apply PushoutCocone.isColimitAux'
  intro s
  refine ⟨presheafedPushoutDesc w hT hS s, presheafedPushoutDesc_inl w hT hS s,
    presheafedPushoutDesc_inr w hT hS s, ?_⟩
  intro m hm hn
  apply presheafedPushout_hom_ext w hT hS
  · exact hm.trans (presheafedPushoutDesc_inl w hT hS s).symm
  · exact hn.trans (presheafedPushoutDesc_inr w hT hS s).symm

include w hT hS in
theorem isPushout_presheafedSpace :
    IsPushout f g i j :=
  IsPushout.of_isColimit (presheafedPushoutIsColimit w hT hS)

end Criterion

end Langlands.AlgebraicGeometry.AffineSchemePushout

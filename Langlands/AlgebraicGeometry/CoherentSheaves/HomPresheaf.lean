import Langlands.AlgebraicGeometry.CoherentSheaves.IsomPresheaf

/-! # Actual Hom presheaves of coherent families -/

noncomputable section

universe v v' u u'

open CategoryTheory CategoryTheory.Bicategory AlgebraicGeometry Opposite
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

private lemma presheafHom_map_identity {C : Type u} [Category.{v} C]
    (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}) {X : C}
    (M : F.obj (.mk (op X))) {Z W : Over X} (q : W ⟶ Z) :
    (F.presheafHom M M).map q.op (𝟙 _) = 𝟙 _ := by
  simp [Pseudofunctor.presheafHom, pullHom,
    ← reassoc_of% Cat.Hom₂.comp_app, ← Cat.Hom₂.comp_app]

private lemma presheafHom_map_composition {C : Type u} [Category.{v} C]
    (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}) {X : C}
    {M N P : F.obj (.mk (op X))} {Z W : Over X} (q : W ⟶ Z)
    (a : (F.presheafHom M N).obj (op Z))
    (b : (F.presheafHom N P).obj (op Z)) :
    (F.presheafHom M P).map q.op (a ≫ b) =
      (F.presheafHom M N).map q.op a ≫ (F.presheafHom N P).map q.op b := by
  simp [Pseudofunctor.presheafHom, pullHom,
    ← reassoc_of% Cat.Hom₂.comp_app, ← Cat.Hom₂.comp_app]

namespace Langlands.AlgebraicGeometry.CoherentSheaves.FamilyGroupoid

set_option backward.isDefEq.respectTransparency false

variable {S X : Scheme.{u}} (f : X ⟶ S) {T : Over S}

/-- All actual module maps between ordinary pullbacks of coherent families,
with coherent restrictions and the explicit value-universe lift. -/
def homPresheaf (M N : FamilyGroupoid f T) : AlgebraicSpace.Presheaf T.left :=
  T.iteratedSliceBackward.op ⋙
    ((Family.pseudofunctor f).presheafHom M.of N.of ⋙ uliftFunctor.{u + 1})

/-- A section is precisely a lifted map of the actual pulled-back modules. -/
def homPointsEquiv (M N : FamilyGroupoid f T) (Z : Over T.left) :
    (homPresheaf f M N).obj (op Z) ≃
      ULift.{u + 1}
        (((pullback f (testMap T Z)).obj M).of.obj ⟶
          ((pullback f (testMap T Z)).obj N).of.obj) where
  toFun a := ULift.up a.down.hom
  invFun a := ULift.up (ObjectProperty.homMk a.down)
  left_inv a := by
    apply ULift.ext
    apply ObjectProperty.hom_ext
    rfl
  right_inv a := rfl

/-- Identity in every fibre of the actual Hom presheaf. -/
def homIdentity (M : FamilyGroupoid f T) (Z : Over T.left) :
    (homPresheaf f M M).obj (op Z) := ULift.up (𝟙 _)

/-- Fibrewise composition retains the underlying actual module maps. -/
def homCompose {M N P : FamilyGroupoid f T} {Z : Over T.left}
    (a : (homPresheaf f M N).obj (op Z))
    (b : (homPresheaf f N P).obj (op Z)) :
    (homPresheaf f M P).obj (op Z) := ULift.up (a.down ≫ b.down)

@[simp]
lemma homIdentity_comp {M N : FamilyGroupoid f T} {Z : Over T.left}
    (a : (homPresheaf f M N).obj (op Z)) :
    homCompose f (homIdentity f M Z) a = a := by
  apply ULift.ext
  exact Category.id_comp _

@[simp]
lemma homCompose_identity {M N : FamilyGroupoid f T} {Z : Over T.left}
    (a : (homPresheaf f M N).obj (op Z)) :
    homCompose f a (homIdentity f N Z) = a := by
  apply ULift.ext
  exact Category.comp_id _

/-- Coherent restriction carries the actual identity to the actual identity. -/
@[simp]
lemma homPresheaf_map_identity (M : FamilyGroupoid f T) {Z W : Over T.left}
    (q : W ⟶ Z) :
    (homPresheaf f M M).map q.op (homIdentity f M Z) = homIdentity f M W := by
  apply ULift.ext
  exact presheafHom_map_identity (Family.pseudofunctor f) M.of
    (T.iteratedSliceBackward.map q)

/-- Coherent restriction preserves composition, including its comparison maps. -/
@[simp]
lemma homPresheaf_map_comp {M N P : FamilyGroupoid f T} {Z W : Over T.left}
    (q : W ⟶ Z) (a : (homPresheaf f M N).obj (op Z))
    (b : (homPresheaf f N P).obj (op Z)) :
    (homPresheaf f M P).map q.op (homCompose f a b) =
      homCompose f ((homPresheaf f M N).map q.op a)
        ((homPresheaf f N P).map q.op b) := by
  apply ULift.ext
  exact presheafHom_map_composition (Family.pseudofunctor f)
    (T.iteratedSliceBackward.map q) a.down b.down

end Langlands.AlgebraicGeometry.CoherentSheaves.FamilyGroupoid

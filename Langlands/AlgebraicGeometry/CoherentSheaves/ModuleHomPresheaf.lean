import Langlands.AlgebraicGeometry.CoherentSheaves.HomPresheaf

/-! # Forgetting family conditions in the actual Hom presheaf -/

noncomputable section

universe v v' u u'

open CategoryTheory CategoryTheory.Bicategory AlgebraicGeometry Opposite
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace Langlands.AlgebraicGeometry.CoherentSheaves

set_option backward.isDefEq.respectTransparency false

private lemma fullsubcategory_pullHom_hom {C : Type u} [Category.{v} C]
    (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'})
    (P : F.ObjectProperty) [P.IsClosedUnderMapObj]
    {T₁ T₂ Y Y' : C}
    {M : P.Obj (.mk (op T₁))} {N : P.Obj (.mk (op T₂))}
    {h₁ : Y ⟶ T₁} {h₂ : Y ⟶ T₂}
    (b : (P.fullsubcategory.map h₁.op.toLoc).toFunctor.obj M ⟶
      (P.fullsubcategory.map h₂.op.toLoc).toFunctor.obj N)
    (g : Y' ⟶ Y) (gh₁ : Y' ⟶ T₁) (gh₂ : Y' ⟶ T₂)
    (e₁ : g ≫ h₁ = gh₁) (e₂ : g ≫ h₂ = gh₂) :
    (pullHom b g gh₁ gh₂ e₁ e₂).hom =
      pullHom (F := F) b.hom g gh₁ gh₂ e₁ e₂ := by
  subst gh₁ gh₂
  dsimp [pullHom]
  simp only [Pseudofunctor.mapComp'_eq_mapComp]
  rfl

/-- The full-subcategory inclusion identifies all Hom sections and restrictions. -/
def fullsubcategoryPresheafHomIso {C : Type u} [Category.{v} C]
    (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'})
    (P : F.ObjectProperty) [P.IsClosedUnderMapObj]
    {B : C} (M N : P.Obj (.mk (op B))) :
    P.fullsubcategory.presheafHom M N ≅ F.presheafHom M.obj N.obj :=
  NatIso.ofComponents (fun _ ↦ Equiv.toIso
    { toFun := fun b ↦ b.hom
      invFun := fun b ↦ ObjectProperty.homMk b
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }) (by
    intro Z Z' q
    apply ConcreteCategory.hom_ext
    intro b
    exact fullsubcategory_pullHom_hom F P b q.unop.left
      Z'.unop.hom Z'.unop.hom q.unop.w q.unop.w)

variable {S X : Scheme.{u}} (f : X ⟶ S) {T : Over S}

/-- All maps of ordinary pulled-back modules on the actual relative spaces,
without family conditions, on the entire slice and with explicit value lift. -/
def moduleHomPresheaf
    (M N : ((Picard.relativeSpace f).obj T).Modules) :
    AlgebraicSpace.Presheaf T.left :=
  T.iteratedSliceBackward.op ⋙
    ((modulePseudofunctor f).presheafHom M N ⋙ uliftFunctor.{u + 1})

/-- The fibre is the type of all maps of the actual ordinary module pullbacks. -/
def moduleHomPointsEquiv
    (M N : ((Picard.relativeSpace f).obj T).Modules) (Z : Over T.left) :
    (moduleHomPresheaf f M N).obj (op Z) ≃
      ULift.{u + 1}
        ((Scheme.Modules.pullback
            ((Picard.relativeSpace f).map (FamilyGroupoid.testMap T Z))).obj M ⟶
          (Scheme.Modules.pullback
            ((Picard.relativeSpace f).map (FamilyGroupoid.testMap T Z))).obj N) :=
  Equiv.refl _

namespace FamilyGroupoid

/-- Forgetting the full family subcategory gives a full-slice natural
isomorphism with the Hom presheaf of the actual underlying modules. -/
def homPresheafModuleIso (M N : FamilyGroupoid f T) :
    homPresheaf f M N ≅ moduleHomPresheaf f M.of.obj N.of.obj :=
  Functor.isoWhiskerLeft T.iteratedSliceBackward.op
    (Functor.isoWhiskerRight
      (fullsubcategoryPresheafHomIso (modulePseudofunctor f) (familyProperty f)
        M.of N.of) uliftFunctor.{u + 1})

/-- The comparison applies the identity to each underlying actual module map. -/
@[simp]
lemma homPresheafModuleIso_hom_app (M N : FamilyGroupoid f T)
    (Z : Over T.left) (a : (homPresheaf f M N).obj (op Z)) :
    (homPresheafModuleIso f M N).hom.app (op Z) a = ULift.up a.down.hom := rfl

/-- The inverse only wraps a module map in the full family subcategory. -/
@[simp]
lemma homPresheafModuleIso_inv_app (M N : FamilyGroupoid f T)
    (Z : Over T.left) (a : (moduleHomPresheaf f M.of.obj N.of.obj).obj (op Z)) :
    (homPresheafModuleIso f M N).inv.app (op Z) a =
      ULift.up (ObjectProperty.homMk a.down) := rfl

end FamilyGroupoid

end Langlands.AlgebraicGeometry.CoherentSheaves

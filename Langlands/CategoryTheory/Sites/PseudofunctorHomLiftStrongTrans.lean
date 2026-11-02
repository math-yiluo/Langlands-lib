import Langlands.CategoryTheory.Sites.PseudofunctorHomLift
import Langlands.CategoryTheory.Sites.PseudofunctorPointFiberTransport

/-! # Strong transformations through the explicit hom-universe lift -/

noncomputable section

universe w v v' u u'

open CategoryTheory CategoryTheory.Bicategory Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.CategoryTheory.PseudofunctorHomLift

variable {A B : Type*} [Category* A] [Category* B] (H : A ⥤ B)

/-- Lifting the morphisms of a fully faithful functor preserves full faithfulness. -/
def liftFunctorFullyFaithful (hH : H.FullyFaithful) :
    (liftFunctor.{w} H).FullyFaithful where
  preimage a := ULift.up (hH.preimage a.down)
  map_preimage a := by
    apply ULift.ext
    exact hH.map_preimage a.down
  preimage_map a := by
    apply ULift.ext
    exact hH.preimage_map a.down

variable {C : Type u} [Category.{v} C]
  {F G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
  (α : Pseudofunctor.StrongTrans F G)

private lemma lifted_comp_down {D : Type*} [Category* D]
    {a b c : ULiftHom.{w} D} (f : a ⟶ b) (g : b ⟶ c) :
    (f ≫ g).down = f.down ≫ g.down := rfl

private lemma lifted_up_down {D : Type*} [Category* D] {a b : D} (f : a ⟶ b) :
    ((ULiftHom.up : D ⥤ ULiftHom.{w} D).map f).down = f := rfl

/-- Lift a strong transformation, retaining its components and coherence maps. -/
def homLiftStrongTrans :
    Pseudofunctor.StrongTrans (homLift.{w} F) (homLift.{w} G) where
  app X := (liftFunctor.{w} (α.app X).toFunctor).toCatHom
  naturality f :=
    Cat.Hom.isoMk (liftNatIso.{w} (Cat.Hom.toNatIso (α.naturality f)))
  naturality_naturality {a b} {f g} η := by
    obtain rfl := LocallyDiscrete.eq_of_hom η
    have hη : η = 𝟙 f := Subsingleton.elim _ _
    subst η
    simp
  naturality_id X := by
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext M
    apply ULift.ext
    dsimp [homLift, liftFunctor, liftNatIso, Cat.Hom.isoMk]
    simpa only [Cat.Hom₂.comp_app, Cat.whiskerRight_app, Cat.whiskerLeft_app,
      Cat.associator_hom_app, Cat.leftUnitor_hom_app, Cat.rightUnitor_inv_app,
      eqToHom_refl, lifted_comp_down, lifted_up_down, ULift.down_up,
      Category.comp_id, Category.id_comp] using
      congrArg (fun e ↦ e.toNatTrans.app M.objDown) (α.naturality_id X)
  naturality_comp {a b c} f g := by
    rcases a with ⟨a⟩
    rcases b with ⟨b⟩
    rcases c with ⟨c⟩
    rcases f with ⟨f⟩
    rcases g with ⟨g⟩
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext M
    apply ULift.ext
    dsimp [homLift, liftFunctor, liftNatIso, Cat.Hom.isoMk]
    simpa only [Cat.Hom₂.comp_app, Cat.whiskerRight_app, Cat.whiskerLeft_app,
      Cat.associator_hom_app, Cat.associator_inv_app,
      Cat.Hom.comp_toFunctor, Functor.comp_obj, Quiver.Hom.toLoc,
      eqToHom_refl, lifted_comp_down, lifted_up_down, ULift.down_up,
      Category.comp_id, Category.id_comp] using
      congrArg (fun e ↦ e.toNatTrans.app M.objDown) (α.naturality_comp f.toLoc g.toLoc)

/-- The lifted fibre component is the explicit lifted original component. -/
lemma homLiftStrongTrans_component (X : C) :
    PseudofunctorPointFiberTransport.component (homLiftStrongTrans.{w} α) X =
      liftFunctor.{w} (PseudofunctorPointFiberTransport.component α X) := rfl

/-- The object action is unchanged through the explicit lift. -/
lemma homLiftStrongTrans_obj (X : C)
    (M : (homLift.{w} F).obj (.mk (op X))) :
    (PseudofunctorPointFiberTransport.component (homLiftStrongTrans.{w} α) X).obj M =
      ULiftHom.objUp.{u', w}
        ((PseudofunctorPointFiberTransport.component α X).obj
          (ULiftHom.objDown.{u', w} M)) := rfl

/-- Fibrewise full faithfulness survives lifting the hom universe. -/
def homLiftStrongTransFullyFaithful
    (hα : ∀ X : C, (PseudofunctorPointFiberTransport.component α X).FullyFaithful)
    (X : C) :
    (PseudofunctorPointFiberTransport.component (homLiftStrongTrans.{w} α) X).FullyFaithful :=
  liftFunctorFullyFaithful _ (hα X)

end Langlands.CategoryTheory.PseudofunctorHomLift

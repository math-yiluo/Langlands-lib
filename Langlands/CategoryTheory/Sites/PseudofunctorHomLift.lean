import Langlands.CategoryTheory.Sites.PseudofunctorPointFiber
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

/-! # Lifting the morphism universe of an actual category-valued pseudofunctor -/

universe w v v' u u'

open CategoryTheory CategoryTheory.Bicategory Opposite

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.CategoryTheory.PseudofunctorHomLift

variable {A B : Type*} [Category* A] [Category* B]

/-- Apply a functor while retaining the explicit lifts of its morphisms. -/
def liftFunctor (G : A ⥤ B) : ULiftHom.{w} A ⥤ ULiftHom.{w} B where
  obj a := ULiftHom.objUp (G.obj a.objDown)
  map f := ULift.up (G.map f.down)
  map_id a := congrArg ULift.up (G.map_id a.objDown)
  map_comp f g := congrArg ULift.up (G.map_comp f.down g.down)

/-- Lift every component of a natural isomorphism. -/
def liftNatIso {G H : A ⥤ B} (e : G ≅ H) : liftFunctor.{w} G ≅ liftFunctor.{w} H :=
  NatIso.ofComponents (fun a ↦ (ULiftHom.up : B ⥤ ULiftHom.{w} B).mapIso (e.app a.objDown)) (by
    intro a b f
    exact congrArg ULift.up (e.hom.naturality f.down))

private lemma comp_down {A : Type*} [Category* A]
    {a b c : ULiftHom.{w} A} (f : a ⟶ b) (g : b ⟶ c) :
    (f ≫ g).down = f.down ≫ g.down := rfl

private lemma up_down {A : Type*} [Category* A] {a b : A} (f : a ⟶ b) :
    ((ULiftHom.up : A ⥤ ULiftHom.{w} A).map f).down = f := rfl

private lemma eqToHom_down {A : Type*} [Category* A]
    {a b : ULiftHom.{w} A} (h : a = b) :
    (eqToHom h).down = eqToHom (congrArg ULiftHom.objDown h) := by
  cases h
  rfl

variable {C : Type u} [Category.{v} C]
  (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'})

/-- Lift fibre morphisms, leaving all fibre objects and base maps unchanged. -/
def homLift : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{max w v', u'} :=
  LocallyDiscrete.mkPseudofunctor
    (fun X ↦ Cat.of (ULiftHom.{w} (F.obj (.mk X))))
    (fun f ↦ (liftFunctor.{w} (F.map f.toLoc).toFunctor).toCatHom)
    (fun X ↦ Cat.Hom.isoMk (liftNatIso.{w} (Cat.Hom.toNatIso (F.mapId (.mk X)))))
    (fun f g ↦ Cat.Hom.isoMk
      (liftNatIso.{w} (Cat.Hom.toNatIso (F.mapComp f.toLoc g.toLoc))))
    (fun f g h ↦ by
      apply Cat.Hom₂.ext
      apply NatTrans.ext
      funext M
      apply ULift.ext
      dsimp [liftFunctor, liftNatIso, Cat.Hom.isoMk]
      rw [Cat.eqToHom_app, eqToHom_down (A := F.obj (.mk _))]
      simpa only [Cat.Hom₂.comp_app, Cat.whiskerRight_app, Cat.whiskerLeft_app,
        Cat.associator_hom_app, Cat.leftUnitor_hom_app, Cat.rightUnitor_hom_app,
        Strict.associator_eqToIso, Strict.leftUnitor_eqToIso, Strict.rightUnitor_eqToIso,
        eqToIso.hom, PrelaxFunctor.map₂_eqToHom, Cat.eqToHom_app,
        eqToHom_down, Category.comp_id, Category.id_comp,
        comp_down, up_down, ULift.down_up, eqToHom_refl] using
        congrArg (fun e ↦ e.toNatTrans.app M.objDown)
          (F.map₂_associator f.toLoc g.toLoc h.toLoc).symm)
    (fun f ↦ by
      apply Cat.Hom₂.ext
      apply NatTrans.ext
      funext M
      apply ULift.ext
      dsimp [liftFunctor, liftNatIso, Cat.Hom.isoMk]
      rw [Cat.eqToHom_app, eqToHom_down (A := F.obj (.mk _))]
      simpa only [Cat.Hom₂.comp_app, Cat.whiskerRight_app, Cat.whiskerLeft_app,
        Cat.associator_hom_app, Cat.leftUnitor_hom_app, Cat.rightUnitor_hom_app,
        Strict.associator_eqToIso, Strict.leftUnitor_eqToIso, Strict.rightUnitor_eqToIso,
        eqToIso.hom, PrelaxFunctor.map₂_eqToHom, Cat.eqToHom_app,
        eqToHom_down, Category.comp_id, Category.id_comp,
        comp_down, up_down, ULift.down_up, eqToHom_refl] using
        congrArg (fun e ↦ e.toNatTrans.app M.objDown)
          (F.map₂_left_unitor f.toLoc).symm)
    (fun f ↦ by
      apply Cat.Hom₂.ext
      apply NatTrans.ext
      funext M
      apply ULift.ext
      dsimp [liftFunctor, liftNatIso, Cat.Hom.isoMk]
      rw [Cat.eqToHom_app, eqToHom_down (A := F.obj (.mk _))]
      simpa only [Cat.Hom₂.comp_app, Cat.whiskerRight_app, Cat.whiskerLeft_app,
        Cat.associator_hom_app, Cat.leftUnitor_hom_app, Cat.rightUnitor_hom_app,
        Strict.associator_eqToIso, Strict.leftUnitor_eqToIso, Strict.rightUnitor_eqToIso,
        eqToIso.hom, PrelaxFunctor.map₂_eqToHom, Cat.eqToHom_app,
        eqToHom_down, Category.comp_id, Category.id_comp,
        comp_down, up_down, ULift.down_up, eqToHom_refl] using
        congrArg (fun e ↦ e.toNatTrans.app M.objDown)
          (F.map₂_right_unitor f.toLoc).symm)

open Langlands.CategoryTheory.PseudofunctorPointFiber

variable {F} {U T : C} (ξ : F.obj (.mk (op U))) (η : F.obj (.mk (op T)))

/-- A lifted actual point is exactly a lift of the original actual point. -/
def pointsEquiv (Z : Over T) :
    Points (homLift.{w} F) (ULiftHom.objUp.{u', w} ξ) (ULiftHom.objUp.{u', w} η) Z ≃
      ULift.{w} (Points F ξ η Z) where
  toFun x := ULift.up ⟨x.1, ULiftHom.down.mapIso x.2⟩
  invFun x := ⟨x.down.1, ULiftHom.up.mapIso x.down.2⟩
  left_inv x := by
    rcases x with ⟨a, e⟩
    congr 1
  right_inv x := by
    rcases x with ⟨a, e⟩
    congr 1

/-- Forgetting the morphism lift commutes with coherent isomorphism pullback. -/
lemma pullIso_down {X₁ X₂ Y Y' : C}
    {M₁ : F.obj (.mk (op X₁))} {M₂ : F.obj (.mk (op X₂))}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (e : ((homLift.{w} F).map f₁.op.toLoc).toFunctor.obj (ULiftHom.objUp.{u', w} M₁) ≅
      ((homLift.{w} F).map f₂.op.toLoc).toFunctor.obj (ULiftHom.objUp.{u', w} M₂))
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (h₁ : g ≫ f₁ = gf₁) (h₂ : g ≫ f₂ = gf₂) :
    (ULiftHom.down (C := F.obj (.mk (op Y')))).mapIso
      (pullIso (F := homLift.{w} F) e g gf₁ gf₂ h₁ h₂) =
      pullIso (F := F) (ULiftHom.down.mapIso e) g gf₁ gf₂ h₁ h₂ := by
  subst gf₁ gf₂
  apply Iso.ext
  dsimp [pullIso]
  simp only [Pseudofunctor.mapComp'_eq_mapComp]
  rfl

/-- The point equivalence commutes with every morphism in the full slice. -/
lemma pointsEquiv_restrict {Z Z' : Over T} (q : Z' ⟶ Z)
    (x : Points (homLift.{w} F) (ULiftHom.objUp.{u', w} ξ) (ULiftHom.objUp.{u', w} η) Z) :
    pointsEquiv.{w} (F := F) ξ η Z' (restrict (homLift.{w} F) _ _ q x) =
      ULift.up (restrict F ξ η q (pointsEquiv.{w} (F := F) ξ η Z x).down) := by
  rcases x with ⟨a, e⟩
  apply ULift.ext
  dsimp [pointsEquiv, restrict]
  congr 1
  exact pullIso_down.{w} (F := F) e q.left _ _ rfl q.w

/-- Natural comparison on the entire slice, including all restriction maps. -/
def presheafIso :
    presheaf (homLift.{w} F) (ULiftHom.objUp.{u', w} ξ) (ULiftHom.objUp.{u', w} η) ≅
      presheaf F ξ η ⋙ uliftFunctor.{w} :=
  NatIso.ofComponents (fun Z ↦ (pointsEquiv.{w} (F := F) ξ η Z.unop).toIso) (by
    intro Z Z' q
    apply ConcreteCategory.hom_ext
    intro x
    exact pointsEquiv_restrict.{w} (F := F) ξ η q.unop x)

end Langlands.CategoryTheory.PseudofunctorHomLift

import Langlands.CategoryTheory.Sites.PseudofunctorPointFiber
import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo
import Mathlib.CategoryTheory.Functor.FullyFaithful

/-! # Actual point fibres under fully faithful strong transformations -/

universe v v' u u'

open CategoryTheory CategoryTheory.Bicategory Opposite

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.CategoryTheory.PseudofunctorPointFiberTransport

variable {C : Type u} [Category.{v} C]
  {F G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
  (α : Pseudofunctor.StrongTrans F G)

/-- The component functor on an actual fibre. -/
abbrev component (X : C) : F.obj (.mk (op X)) ⥤ G.obj (.mk (op X)) :=
  (α.app (.mk (op X))).toFunctor

/-- The actual isomorphism comparing the two orders of pullback and transport. -/
def comparison {X Y : C} (f : Y ⟶ X) (ξ : F.obj (.mk (op X))) :
    (component α Y).obj ((F.map f.op.toLoc).toFunctor.obj ξ) ≅
      (G.map f.op.toLoc).toFunctor.obj ((component α X).obj ξ) :=
  (Cat.Hom.toNatIso (α.naturality f.op.toLoc)).app ξ

/-- The comparison retains the original composition coherence. -/
lemma comparison_comp {X Y Z : C} (f : Y ⟶ X) (g : Z ⟶ Y)
    (ξ : F.obj (.mk (op X))) :
    comparison α (g ≫ f) ξ =
      (component α Z).mapIso ((Cat.Hom.toNatIso (F.mapComp f.op.toLoc g.op.toLoc)).app ξ) ≪≫
        comparison α g ((F.map f.op.toLoc).toFunctor.obj ξ) ≪≫
          (G.map g.op.toLoc).toFunctor.mapIso (comparison α f ξ) ≪≫
            ((Cat.Hom.toNatIso (G.mapComp f.op.toLoc g.op.toLoc)).app
              ((component α X).obj ξ)).symm := by
  apply Iso.ext
  simpa only [comparison, component, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Cat.Hom.toNatIso, Iso.app,
    Cat.Hom₂.comp_app, Cat.whiskerRight_app, Cat.whiskerLeft_app,
    Cat.associator_hom_app, Cat.associator_inv_app,
    eqToHom_refl, Category.comp_id, Category.id_comp, op_comp,
    Quiver.Hom.comp_toLoc, Cat.Hom.comp_toFunctor, Functor.comp_obj] using
    congrArg (fun e ↦ e.toNatTrans.app ξ)
      (Pseudofunctor.StrongTrans.naturality_comp_hom α f.op.toLoc g.op.toLoc)

open Langlands.CategoryTheory.PseudofunctorPointFiber

variable {U T : C} (ξ : F.obj (.mk (op U))) (η : F.obj (.mk (op T)))

/-- Transport an actual isomorphism between two pullbacks. -/
def transportIso {Z : C} (a : Z ⟶ U) (p : Z ⟶ T)
    (e : (F.map a.op.toLoc).toFunctor.obj ξ ≅ (F.map p.op.toLoc).toFunctor.obj η) :
    (G.map a.op.toLoc).toFunctor.obj ((component α U).obj ξ) ≅
      (G.map p.op.toLoc).toFunctor.obj ((component α T).obj η) :=
  (comparison α a ξ).symm ≪≫ (component α Z).mapIso e ≪≫ comparison α p η

/-- A strong transformation maps actual points without changing the base map. -/
def mapPoints (Z : Over T) : Points F ξ η Z →
    Points G ((component α U).obj ξ) ((component α T).obj η) Z :=
  fun x ↦ ⟨x.1, transportIso α ξ η x.1 Z.hom x.2⟩

/-- Transport commutes with the full coherent pullback of actual isomorphisms. -/
lemma transportIso_pullIso {Z Z' : C} {a : Z ⟶ U} {p : Z ⟶ T}
    (e : (F.map a.op.toLoc).toFunctor.obj ξ ≅ (F.map p.op.toLoc).toFunctor.obj η)
    (q : Z' ⟶ Z) (qa : Z' ⟶ U) (qp : Z' ⟶ T)
    (ha : q ≫ a = qa) (hp : q ≫ p = qp) :
    transportIso α ξ η qa qp (pullIso (F := F) e q qa qp ha hp) =
      pullIso (F := G) (transportIso α ξ η a p e) q qa qp ha hp := by
  subst qa qp
  apply Iso.ext
  simp only [transportIso, comparison_comp, pullIso, op_comp,
    Quiver.Hom.comp_toLoc, Cat.Hom.comp_toFunctor, Functor.comp_obj,
    Pseudofunctor.mapComp'_eq_mapComp, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.mapIso_inv, Iso.trans_inv, Iso.symm_inv,
    Functor.map_comp, Category.assoc]
  simp only [Iso.map_inv_hom_id_assoc]
  simp only [comparison, Iso.app_hom, Iso.app_inv]
  have hn := NatIso.naturality_1 (Cat.Hom.toNatIso (α.naturality q.op.toLoc)) e.hom
  simp only [Cat.Hom.comp_toFunctor, Functor.comp_map] at hn
  rw [reassoc_of% hn]

/-- Every restriction in the entire slice commutes with point transport. -/
lemma mapPoints_restrict {Z Z' : Over T} (q : Z' ⟶ Z) (x : Points F ξ η Z) :
    mapPoints α ξ η Z' (restrict F ξ η q x) =
      restrict G ((component α U).obj ξ) ((component α T).obj η) q
        (mapPoints α ξ η Z x) := by
  rcases x with ⟨a, e⟩
  dsimp [mapPoints, restrict]
  congr 1
  exact transportIso_pullIso α ξ η e q.left _ _ rfl q.w

/-- The actual point map is a natural transformation of the full presheaves. -/
def presheafMap : presheaf F ξ η ⟶
    presheaf G ((component α U).obj ξ) ((component α T).obj η) where
  app Z := ↾(mapPoints α ξ η Z.unop)
  naturality {_ _} q := by
    apply ConcreteCategory.hom_ext
    intro x
    exact mapPoints_restrict α ξ η q.unop x

private def isoConjugationEquiv {D : Type*} [Category* D] {A B A' B' : D}
    (a : A' ≅ A) (b : B ≅ B') : (A ≅ B) ≃ (A' ≅ B') where
  toFun e := a ≪≫ e ≪≫ b
  invFun e := a.symm ≪≫ e ≪≫ b.symm
  left_inv e := by simp
  right_inv e := by simp

/-- Fully faithful fibre components give equivalences on actual point types. -/
def pointsEquiv (hα : ∀ Z : C, (component α Z).FullyFaithful) (Z : Over T) :
    Points F ξ η Z ≃ Points G ((component α U).obj ξ) ((component α T).obj η) Z :=
  Equiv.sigmaCongrRight (fun a ↦ (hα Z.left).isoEquiv.trans
    (isoConjugationEquiv (comparison α a ξ).symm (comparison α Z.hom η)))

/-- The equivalence's forward map is the explicit actual point map. -/
lemma pointsEquiv_apply (hα : ∀ Z : C, (component α Z).FullyFaithful)
    (Z : Over T) (x : Points F ξ η Z) :
    pointsEquiv α ξ η hα Z x = mapPoints α ξ η Z x := rfl

/-- A fibrewise fully faithful strong transformation preserves the whole actual
point-fibre presheaf, with its coherent restriction maps. -/
def presheafIso (hα : ∀ Z : C, (component α Z).FullyFaithful) :
    presheaf F ξ η ≅ presheaf G ((component α U).obj ξ) ((component α T).obj η) :=
  NatIso.ofComponents (fun Z ↦ (pointsEquiv α ξ η hα Z.unop).toIso) (by
    intro Z Z' q
    apply ConcreteCategory.hom_ext
    intro x
    exact mapPoints_restrict α ξ η q.unop x)

end Langlands.CategoryTheory.PseudofunctorPointFiberTransport

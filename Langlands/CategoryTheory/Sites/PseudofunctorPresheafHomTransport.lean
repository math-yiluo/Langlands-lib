import Langlands.CategoryTheory.Sites.PseudofunctorPointFiberTransport

/-! # Morphism presheaves under fully faithful strong transformations -/

universe v v' u u'

open CategoryTheory CategoryTheory.Bicategory Opposite

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.CategoryTheory.PseudofunctorPresheafHomTransport

open Langlands.CategoryTheory.PseudofunctorPointFiberTransport
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C]
  {F G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
  (α : Pseudofunctor.StrongTrans F G)

section

variable {U T : C} (ξ : F.obj (.mk (op U))) (η : F.obj (.mk (op T)))

/-- Transport an actual morphism between two pullbacks. -/
def transportHom {Z : C} (a : Z ⟶ U) (p : Z ⟶ T)
    (φ : (F.map a.op.toLoc).toFunctor.obj ξ ⟶ (F.map p.op.toLoc).toFunctor.obj η) :
    (G.map a.op.toLoc).toFunctor.obj ((component α U).obj ξ) ⟶
      (G.map p.op.toLoc).toFunctor.obj ((component α T).obj η) :=
  (comparison α a ξ).inv ≫ (component α Z).map φ ≫ (comparison α p η).hom

/-- Transport commutes with the full coherent pullback of actual morphisms. -/
lemma transportHom_pullHom {Z Z' : C} {a : Z ⟶ U} {p : Z ⟶ T}
    (φ : (F.map a.op.toLoc).toFunctor.obj ξ ⟶ (F.map p.op.toLoc).toFunctor.obj η)
    (q : Z' ⟶ Z) (qa : Z' ⟶ U) (qp : Z' ⟶ T)
    (ha : q ≫ a = qa) (hp : q ≫ p = qp) :
    transportHom α ξ η qa qp (pullHom (F := F) φ q qa qp ha hp) =
      pullHom (F := G) (transportHom α ξ η a p φ) q qa qp ha hp := by
  subst qa qp
  simp only [transportHom, comparison_comp, pullHom, op_comp,
    Quiver.Hom.comp_toLoc, Cat.Hom.comp_toFunctor, Functor.comp_obj,
    Pseudofunctor.mapComp'_eq_mapComp, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.mapIso_inv, Iso.trans_inv, Iso.symm_inv,
    Functor.map_comp, Category.assoc]
  simp only [Iso.app_hom, Iso.app_inv, Cat.Hom.toNatIso_hom, Cat.Hom.toNatIso_inv]
  have h₁ : (component α Z').map ((F.mapComp a.op.toLoc q.op.toLoc).inv.toNatTrans.app ξ) ≫
      (component α Z').map ((F.mapComp a.op.toLoc q.op.toLoc).hom.toNatTrans.app ξ) =
        𝟙 _ := by
    rw [← Functor.map_comp, Cat.Hom.inv_hom_id_toNatTrans_app, CategoryTheory.Functor.map_id]
  have h₂ : (component α Z').map ((F.mapComp p.op.toLoc q.op.toLoc).inv.toNatTrans.app η) ≫
      (component α Z').map ((F.mapComp p.op.toLoc q.op.toLoc).hom.toNatTrans.app η) =
        𝟙 _ := by
    rw [← Functor.map_comp, Cat.Hom.inv_hom_id_toNatTrans_app, CategoryTheory.Functor.map_id]
  simp only [reassoc_of% h₁, reassoc_of% h₂]
  simp only [comparison, Iso.app_hom, Iso.app_inv]
  have hn := NatIso.naturality_1 (Cat.Hom.toNatIso (α.naturality q.op.toLoc)) φ
  simp only [Cat.Hom.comp_toFunctor, Functor.comp_map] at hn
  rw [reassoc_of% hn]

end

variable {S : C} (M N : F.obj (.mk (op S)))

/-- The actual morphism presheaf map induced by a strong transformation, on the
entire slice over `S`. -/
def presheafHomMap : F.presheafHom M N ⟶
    G.presheafHom ((component α S).obj M) ((component α S).obj N) where
  app Z := ↾(transportHom α M N Z.unop.hom Z.unop.hom)
  naturality {_ Z'} q := by
    apply ConcreteCategory.hom_ext
    intro φ
    exact transportHom_pullHom α M N φ q.unop.left Z'.unop.hom Z'.unop.hom
      q.unop.w q.unop.w

private def homConjugationEquiv {D : Type*} [Category* D] {A B A' B' : D}
    (a : A' ≅ A) (b : B ≅ B') : (A ⟶ B) ≃ (A' ⟶ B') where
  toFun φ := a.hom ≫ φ ≫ b.hom
  invFun φ := a.inv ≫ φ ≫ b.inv
  left_inv φ := by simp
  right_inv φ := by simp

/-- Fully faithful fibre components give bijections on actual morphisms. -/
def presheafHomEquiv (hα : ∀ Z : C, (component α Z).FullyFaithful) (Z : Over S) :
    (F.presheafHom M N).obj (op Z) ≃
      (G.presheafHom ((component α S).obj M) ((component α S).obj N)).obj (op Z) :=
  (hα Z.left).homEquiv.trans
    (homConjugationEquiv (comparison α Z.hom M).symm (comparison α Z.hom N))

/-- The bijection's forward map is the explicit transport. -/
lemma presheafHomEquiv_apply (hα : ∀ Z : C, (component α Z).FullyFaithful)
    (Z : Over S) (φ : (F.presheafHom M N).obj (op Z)) :
    presheafHomEquiv α M N hα Z φ = transportHom α M N Z.hom Z.hom φ := rfl

/-- A fibrewise fully faithful strong transformation preserves the whole actual
morphism presheaf, with its coherent restriction maps. -/
def presheafHomIso (hα : ∀ Z : C, (component α Z).FullyFaithful) :
    F.presheafHom M N ≅
      G.presheafHom ((component α S).obj M) ((component α S).obj N) :=
  NatIso.ofComponents (fun Z ↦ (presheafHomEquiv α M N hα Z.unop).toIso) (by
    intro Z Z' q
    apply ConcreteCategory.hom_ext
    intro φ
    exact transportHom_pullHom α M N φ q.unop.left Z'.unop.hom Z'.unop.hom
      q.unop.w q.unop.w)

/-- The isomorphism's forward map is the explicit presheaf map. -/
lemma presheafHomIso_hom (hα : ∀ Z : C, (component α Z).FullyFaithful) :
    (presheafHomIso α M N hα).hom = presheafHomMap α M N := rfl

end Langlands.CategoryTheory.PseudofunctorPresheafHomTransport

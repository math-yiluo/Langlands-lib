import Langlands.AlgebraicGeometry.Picard.Groupoid
import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo

/-! # The actual Picard-to-module strong transformation -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Bicategory AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid

variable {X S : Scheme.{u}}

private lemma pseudofunctor_comp_obj {B C D : Type*} [Bicategory B] [Bicategory C]
    [Bicategory D] (F : B ⥤ᵖ C) (G : C ⥤ᵖ D) (a : B) :
    (F.comp G).obj a = G.obj (F.obj a) := rfl

private lemma picard_obj (a : LocallyDiscrete Scheme.{u}ᵒᵖ) :
    pseudofunctor.obj a = Cat.of (PicardGroupoid a.as.unop) := rfl

private lemma forget_obj (a : Adj Cat) : Adj.forget₁.obj a = a.obj := rfl

private lemma forget_map₂ {a b : Adj Cat} {F G : a ⟶ b} (η : F ⟶ G) :
    Adj.forget₁.map₂ η = η.τl := rfl

private lemma forget_comp_mapComp {B : Type*} [Bicategory B]
    (F : B ⥤ᵖ Adj Cat) {a b c : B} (h : a ⟶ b) (k : b ⟶ c) :
    ((F.comp Adj.forget₁).mapComp h k).hom = (F.mapComp h k).hom.τl := by
  simp only [Pseudofunctor.comp, Iso.trans_hom, PrelaxFunctor.map₂Iso_hom,
    forget_map₂, Adj.forget₁_mapComp, Iso.refl_hom]
  exact Category.comp_id _

private lemma adj_eqToHom_τl {a b : Adj Cat} {F G : a ⟶ b} (e : F = G) :
    (eqToHom e).τl = eqToHom (congrArg Adj.Hom.l e) := by
  cases e
  rfl

private lemma precomp_mapComp_app {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) (G : LocallyDiscrete D ⥤ᵖ Cat)
    {a b c : C} (h : a ⟶ b) (k : b ⟶ c)
    (M : G.obj (.mk (F.obj a))) :
    ((F.toPseudofunctor.comp G).mapComp h.toLoc k.toLoc).hom.toNatTrans.app M =
      eqToHom (congrArg (fun l => (G.map l.toLoc).toFunctor.obj M) (F.map_comp h k)) ≫
        (G.mapComp (F.map h).toLoc (F.map k).toLoc).hom.toNatTrans.app M := by
  simp only [Pseudofunctor.comp, Iso.trans_hom, PrelaxFunctor.map₂Iso_hom,
    Functor.toPseudofunctor_mapComp]
  dsimp only [Quiver.Hom.toLoc]
  simp only [eqToIso.hom, PrelaxFunctor.map₂_eqToHom,
    Cat.Hom.toNatTrans_comp, Cat.Hom₂.eqToHom_toNatTrans, NatTrans.comp_app,
    eqToHom_app]
  rfl

private lemma precomp_adj_mapComp_app {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) (G : LocallyDiscrete D ⥤ᵖ Adj Cat)
    {a b c : C} (h : a ⟶ b) (k : b ⟶ c)
    (M : (G.obj (.mk (F.obj a))).obj) :
    (((F.toPseudofunctor.comp G).comp Adj.forget₁).mapComp h.toLoc k.toLoc).hom.toNatTrans.app M =
      eqToHom (congrArg (fun l => (G.map l.toLoc).l.toFunctor.obj M) (F.map_comp h k)) ≫
        (G.mapComp (F.map h).toLoc (F.map k).toLoc).hom.τl.toNatTrans.app M := by
  rw [forget_comp_mapComp]
  simp only [Pseudofunctor.comp, Iso.trans_hom, PrelaxFunctor.map₂Iso_hom,
    Functor.toPseudofunctor_mapComp]
  dsimp only [Quiver.Hom.toLoc]
  simp only [eqToIso.hom, PrelaxFunctor.map₂_eqToHom, Adj.comp_τl,
    adj_eqToHom_τl, Cat.Hom.toNatTrans_comp, Cat.Hom₂.eqToHom_toNatTrans,
    NatTrans.comp_app, eqToHom_app]
  rfl

private lemma precomp_mapComp_module {C : Type*} [Category* C]
    (F : C ⥤ Scheme.{u}ᵒᵖ) {a b c : C} (h : a ⟶ b) (k : b ⟶ c)
    (L : PicardGroupoid (F.obj a).unop) :
    (((F.toPseudofunctor.comp Scheme.Modules.pseudofunctor).comp Adj.forget₁).mapComp
      h.toLoc k.toLoc).hom.toNatTrans.app L.of.obj =
    (((F.toPseudofunctor.comp pseudofunctor).mapComp h.toLoc k.toLoc).hom.toNatTrans.app
      L).iso.hom.hom := by
  let U : PicardGroupoid (F.obj c).unop ⥤ (F.obj c).unop.Modules :=
    Core.inclusion _ ⋙ LineBundle.forget _
  change _ = U.map (((F.toPseudofunctor.comp pseudofunctor).mapComp
    h.toLoc k.toLoc).hom.toNatTrans.app L)
  rw [precomp_adj_mapComp_app, precomp_mapComp_app]
  simp only [Functor.map_comp, eqToHom_map]
  congr 1

private lemma precomp_mapId_module {C : Type*} [Category* C]
    (F : C ⥤ Scheme.{u}ᵒᵖ) (a : C) (L : PicardGroupoid (F.obj a).unop) :
    (((F.toPseudofunctor.comp Scheme.Modules.pseudofunctor).comp Adj.forget₁).mapId
      (.mk a)).hom.toNatTrans.app L.of.obj =
    (((F.toPseudofunctor.comp pseudofunctor).mapId (.mk a)).hom.toNatTrans.app
      L).iso.hom.hom := by
  let U : PicardGroupoid (F.obj a).unop ⥤ (F.obj a).unop.Modules :=
    Core.inclusion _ ⋙ LineBundle.forget _
  change _ = U.map (((F.toPseudofunctor.comp pseudofunctor).mapId (.mk a)).hom.toNatTrans.app L)
  simp only [Pseudofunctor.comp,
    Iso.trans_hom, PrelaxFunctor.map₂Iso_hom, Functor.toPseudofunctor_mapId,
    eqToIso.hom, PrelaxFunctor.map₂_eqToHom, PrelaxFunctor.map₂_comp,
    Adj.forget₁_mapId, Adj.id_l, Iso.refl_hom, Cat.Hom.toNatTrans_comp,
    Cat.Hom₂.eqToHom_toNatTrans, Cat.Hom.toNatTrans_id, NatTrans.comp_app,
    NatTrans.id_app, eqToHom_app, Functor.map_comp, eqToHom_map]
  simp only [pseudofunctor, LocallyDiscrete.mkPseudofunctor_mapId]
  rfl

private def catStrongTrans {C : Type*} [Category* C]
    (F G : LocallyDiscrete C ⥤ᵖ Cat)
    (A : ∀ a : C, F.obj (.mk a) ⥤ G.obj (.mk a))
    (n : ∀ {a b : C} (h : a ⟶ b),
      (F.map h.toLoc).toFunctor ⋙ A b ≅ A a ⋙ (G.map h.toLoc).toFunctor)
    (hi : ∀ (a : C) (L : F.obj (.mk a)),
      (n (𝟙 a)).hom.app L ≫ (G.mapId (.mk a)).hom.toNatTrans.app ((A a).obj L) =
        (A a).map ((F.mapId (.mk a)).hom.toNatTrans.app L))
    (hc : ∀ {a b c : C} (h : a ⟶ b) (k : b ⟶ c) (L : F.obj (.mk a)),
      (n (h ≫ k)).hom.app L ≫ (G.mapComp h.toLoc k.toLoc).hom.toNatTrans.app ((A a).obj L) =
        (A c).map ((F.mapComp h.toLoc k.toLoc).hom.toNatTrans.app L) ≫
          (n k).hom.app ((F.map h.toLoc).toFunctor.obj L) ≫
            (G.map k.toLoc).toFunctor.map ((n h).hom.app L)) :
    Pseudofunctor.StrongTrans F G where
  app a := (A a.as).toCatHom
  naturality h := Cat.Hom.isoMk (n h.as)
  naturality_naturality η := by
    obtain rfl := obj_ext_of_isDiscrete η
    have hη : η = 𝟙 _ := Subsingleton.elim _ _
    subst hη
    simp only [PrelaxFunctor.map₂_id, id_whiskerRight,
      whiskerLeft_id, Category.id_comp, Category.comp_id]
  naturality_id a := by
    rcases a with ⟨a⟩
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext L
    change (n (𝟙 a)).hom.app L ≫
        (G.mapId (.mk a)).hom.toNatTrans.app ((A a).obj L) =
      (A a).map ((F.mapId (.mk a)).hom.toNatTrans.app L) ≫ 𝟙 _ ≫ 𝟙 _
    simpa only [Category.comp_id] using hi a L
  naturality_comp {a b c} h k := by
    rcases a with ⟨a⟩
    rcases b with ⟨b⟩
    rcases c with ⟨c⟩
    rcases h with ⟨h⟩
    rcases k with ⟨k⟩
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext L
    change (n (h ≫ k)).hom.app L ≫
        (G.mapComp h.toLoc k.toLoc).hom.toNatTrans.app ((A a).obj L) =
      (A c).map ((F.mapComp h.toLoc k.toLoc).hom.toNatTrans.app L) ≫ 𝟙 _ ≫
        (n k).hom.app ((F.map h.toLoc).toFunctor.obj L) ≫ 𝟙 _ ≫
          (G.map k.toLoc).toFunctor.map ((n h).hom.app L) ≫ 𝟙 _
    simpa only [Category.comp_id, Category.id_comp, Category.assoc] using hc h k L

private def moduleNaturality {C : Type*} [Category* C] (F : C ⥤ Scheme.{u}ᵒᵖ)
    {a b : C} (h : a ⟶ b) :
    ((F.toPseudofunctor.comp pseudofunctor).map h.toLoc).toFunctor ⋙
        (Core.inclusion _ ⋙ LineBundle.forget _) ≅
      (Core.inclusion _ ⋙ LineBundle.forget _) ⋙
        (((F.toPseudofunctor.comp Scheme.Modules.pseudofunctor).comp Adj.forget₁).map
          h.toLoc).toFunctor := Iso.refl _

private lemma picard_pullback_obj_module {Y Z : Scheme.{u}} (h : Y ⟶ Z)
    (L : PicardGroupoid Z) :
    ((pullback h).obj L).of.obj = (Scheme.Modules.pullback h).obj L.of.obj := rfl

private lemma precomp_module_mapCat {C : Type*} [Category* C]
    (F : C ⥤ Scheme.{u}ᵒᵖ) {a b : C} (h : a ⟶ b) :
    ((F.toPseudofunctor.comp Scheme.Modules.pseudofunctor).comp Adj.forget₁).map
      h.toLoc = (Scheme.Modules.pullback (F.map h).unop).toCatHom := rfl

private lemma precomp_picard_mapCat {C : Type*} [Category* C]
    (F : C ⥤ Scheme.{u}ᵒᵖ) {a b : C} (h : a ⟶ b) :
    (F.toPseudofunctor.comp pseudofunctor).map h.toLoc =
      (pullback (F.map h).unop).toCatHom := rfl

private lemma moduleNaturality_hom_app {C : Type*} [Category* C]
    (F : C ⥤ Scheme.{u}ᵒᵖ) {a b : C} (h : a ⟶ b)
    (L : PicardGroupoid (F.obj a).unop) :
    (moduleNaturality F h).hom.app L =
      𝟙 ((Scheme.Modules.pullback (F.map h).unop).obj L.of.obj) := rfl

/-- Ordinary pullback carries the actual line-bundle inclusion into module
sheaves to a strong transformation, including the identity and composition
transports of any precomposing functor. -/
def toModuleStrongTrans {C : Type*} [Category* C] (F : C ⥤ Scheme.{u}ᵒᵖ) :
    Pseudofunctor.StrongTrans (F.toPseudofunctor.comp pseudofunctor)
      ((F.toPseudofunctor.comp Scheme.Modules.pseudofunctor).comp Adj.forget₁) :=
  catStrongTrans _ _ (fun _ => Core.inclusion _ ⋙ LineBundle.forget _)
    (moduleNaturality F)
    (fun a L => by
      dsimp only [moduleNaturality, Iso.refl_hom, NatTrans.id_app]
      rw [Category.id_comp]
      exact precomp_mapId_module F a L)
    (fun {a b c} h k L => by
      dsimp (config := { instances := true }) only [Cat.str, Cat.of, Bundled.of,
        pseudofunctor_comp_obj, Functor.toPseudofunctor_obj, forget_obj,
        Scheme.Modules.pseudofunctor_obj_obj, picard_obj] at L ⊢
      rw [moduleNaturality_hom_app, moduleNaturality_hom_app,
        moduleNaturality_hom_app]
      dsimp (config := { instances := true }) only [precomp_module_mapCat,
        precomp_picard_mapCat, Functor.toCatHom_toFunctor,
        Cat.Hom.comp_toFunctor, picard_pullback_obj_module, Functor.comp_obj, Functor.comp_map,
        Core.inclusion, LineBundle.forget, ObjectProperty.ι, inducedFunctor]
      simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
      exact precomp_mapComp_module F h k L)

/-- The component functor retains the actual module sheaf and its underlying
module isomorphism. -/
@[simp]
lemma toModuleStrongTrans_app {C : Type*} [Category* C]
    (F : C ⥤ Scheme.{u}ᵒᵖ) (a : C) :
    ((toModuleStrongTrans F).app (.mk a)).toFunctor =
      Core.inclusion _ ⋙ LineBundle.forget _ := rfl

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid

import Langlands.AlgebraicGeometry.Modules.EqualCompositePullback

/-! # Pullback comparison around a commutative square -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace Langlands.Scheme.Modules

open Langlands.SchemeModule Langlands.SchemeModule.RigidifiedModule

/-- The canonical comparison between the two orders of pullback around a square. -/
def squarePullbackIso {X Y X' Y' : Scheme.{u}}
    (p : X ⟶ Y) (p' : X' ⟶ Y') (s : X' ⟶ X) (t : Y' ⟶ Y)
    (hs : p' ≫ t = s ≫ p) (M : Y.Modules) :
    (Scheme.Modules.pullback p').obj ((Scheme.Modules.pullback t).obj M) ≅
      (Scheme.Modules.pullback s).obj ((Scheme.Modules.pullback p).obj M) :=
  (Scheme.Modules.pullbackComp p' t).app M ≪≫
    (Scheme.Modules.pullbackCongr hs).app M ≪≫ ((Scheme.Modules.pullbackComp s p).app M).symm

/-- Associativity relates the square comparison to any further pullback. -/
lemma squarePullbackIso_comp {V X Y X' Y' : Scheme.{u}}
    (p : X ⟶ Y) (p' : X' ⟶ Y') (s : X' ⟶ X) (t : Y' ⟶ Y)
    (hs : p' ≫ t = s ≫ p) (M : Y.Modules) (a : V ⟶ X') (z : V ⟶ Y)
    (ha : (a ≫ s) ≫ p = z) (ha' : (a ≫ p') ≫ t = z) :
    (Scheme.Modules.pullback a).map (squarePullbackIso p p' s t hs M).hom ≫
        (Scheme.Modules.pullbackComp a s).hom.app ((Scheme.Modules.pullback p).obj M) ≫
          compHom (a ≫ s) p z ha M =
      (Scheme.Modules.pullbackComp a p').hom.app ((Scheme.Modules.pullback t).obj M) ≫
        compHom (a ≫ p') t z ha' M := by
  have hz : a ≫ (s ≫ p) = z := (Category.assoc _ _ _).symm.trans ha
  have e1 := compHom_assoc a s p (a ≫ s) (s ≫ p) z rfl rfl ha hz M
  have e2 := compHom_assoc a p' t (a ≫ p') (s ≫ p) z rfl hs ha' hz M
  simp only [compHom_rfl] at e1 e2
  rw [e1, e2]
  simp only [squarePullbackIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    compHom, Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc (Scheme.Modules.pullback a)
    ((Scheme.Modules.pullbackComp s p).inv.app M), Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- Changing an equal map before a composition comparison has no effect. -/
lemma pullbackCongr_compHom {V Y' Y : Scheme.{u}} (t : Y' ⟶ Y)
    (x y : V ⟶ Y') (h : x = y) (z : V ⟶ Y) (hx : x ≫ t = z) (hy : y ≫ t = z)
    (M : Y.Modules) :
    (Scheme.Modules.pullbackCongr h).hom.app ((Scheme.Modules.pullback t).obj M) ≫
        compHom y t z hy M =
      compHom x t z hx M := by
  subst h
  simp [Scheme.Modules.pullbackCongr]

/-- Canonical equal-composite comparisons commute with a commutative square. -/
lemma equalCompositeIso_square {V X Y X' Y' : Scheme.{u}}
    (p : X ⟶ Y) (p' : X' ⟶ Y') (s : X' ⟶ X) (t : Y' ⟶ Y)
    (hs : p' ≫ t = s ≫ p) (M : Y.Modules) (a b : V ⟶ X')
    (hab : a ≫ p' = b ≫ p') (hab' : (a ≫ s) ≫ p = (b ≫ s) ≫ p) :
    (Scheme.Modules.pullback a).map (squarePullbackIso p p' s t hs M).hom ≫
        (Scheme.Modules.pullbackComp a s).hom.app ((Scheme.Modules.pullback p).obj M) ≫
          (equalCompositeIso p (a ≫ s) (b ≫ s) hab' M).hom =
      (equalCompositeIso p' a b hab ((Scheme.Modules.pullback t).obj M)).hom ≫
        (Scheme.Modules.pullback b).map (squarePullbackIso p p' s t hs M).hom ≫
          (Scheme.Modules.pullbackComp b s).hom.app ((Scheme.Modules.pullback p).obj M) := by
  have hz : (b ≫ p') ≫ t = (b ≫ s) ≫ p := by simp only [Category.assoc, hs]
  rw [← cancel_mono ((Scheme.Modules.pullbackComp (b ≫ s) p).hom.app M)]
  have ea := squarePullbackIso_comp p p' s t hs M a ((b ≫ s) ≫ p) hab'
    ((congrArg (fun q ↦ q ≫ t) hab).trans hz)
  have eb := squarePullbackIso_comp p p' s t hs M b ((b ≫ s) ≫ p) rfl hz
  simp only [compHom_rfl] at eb
  rw [equalCompositeIso_hom_eq_compHom]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [ea, eb]
  rw [equalCompositeIso_hom_eq_compHom]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  conv_rhs => rw [compHom]
  simp only [Category.assoc]
  rw [pullbackCongr_compHom]

/-- The normalized action after a square pullback is the original action on composite maps. -/
lemma equalCompositeUnitAut_square {V X Y X' Y' : Scheme.{u}}
    (p : X ⟶ Y) (p' : X' ⟶ Y') (s : X' ⟶ X) (t : Y' ⟶ Y)
    (hs : p' ≫ t = s ≫ p) {M : Y.Modules}
    (α : (Scheme.Modules.pullback p).obj M ≅ structureModule X) (a b : V ⟶ X')
    (hab : a ≫ p' = b ≫ p') (hab' : (a ≫ s) ≫ p = (b ≫ s) ≫ p) :
    equalCompositeUnitAut p' a b hab
        (squarePullbackIso p p' s t hs M ≪≫ (Scheme.Modules.pullback s).mapIso α ≪≫
          pullbackUnitIso s) =
      equalCompositeUnitAut p (a ≫ s) (b ≫ s) hab' α := by
  ext1
  have hb := (Scheme.Modules.pullbackComp b s).hom.naturality α.hom
  simp only [Functor.comp_map] at hb
  have hu := pullbackUnitIso_inv_comp a s
  have hv := pullbackUnitComposition V X' X b s
  have hc := equalCompositeIso_square p p' s t hs M a b hab hab'
  rw [equalCompositeUnitAut_hom, equalCompositeUnitAut_hom]
  simp only [Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv,
    Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hu]
  rw [← hv]
  erw [reassoc_of% hb]
  rw [← reassoc_of% hc]
  rw [← Functor.map_comp_assoc (Scheme.Modules.pullback a)
    (squarePullbackIso p p' s t hs M).inv, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.id_comp]
  have ha' := (Scheme.Modules.pullbackComp a s).hom.naturality α.inv
  simp only [Functor.comp_map] at ha'
  erw [reassoc_of% ha']
  rfl

end Langlands.Scheme.Modules

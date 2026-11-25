/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.CartesianChartClassPullback
import all WeilConjectures.AlgebraicGeometry.AbelianRawPullbackComposition
import WeilConjectures.SixFunctors.BaseChange.DerivedComparison
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompAssoc
-- Internal comparison lemmas are shared through private imports.
set_option linter.privateModule false

@[expose] public section
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale
set_option backward.isDefEq.respectTransparency true
set_option linter.unusedSimpArgs false
set_option linter.privateModule false

variable (A : Type (u + 2)) [Category.{u + 1} A]
  [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

private lemma comp_single {S Y Z : Scheme.{u}} (a : Z ⟶ Y) (h : Y ⟶ S)
    (h' : Z ⟶ S) (w : h' = a ≫ h)
    (M : Sheaf S.smallEtaleTopology A) :
    (upperStarCompDerivedPlus A a h h' w).hom.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj M) ≫
      D+((a)^*[A]).map
        ((((h)^*[A]).mapDerivedCategoryPlusSingleFunctor 0).hom.app M) ≫
      (((a)^*[A]).mapDerivedCategoryPlusSingleFunctor 0).hom.app _ =
    (((h')^*[A]).mapDerivedCategoryPlusSingleFunctor 0).hom.app M ≫
      (DerivedCategory.Plus.singleFunctor _ 0).map
        ((upperStarComp A a h h' w).hom.app M) := by
  subst h'
  exact singleComp A h a M

private lemma comp_single_inv {S Y Z : Scheme.{u}} (a : Z ⟶ Y) (h : Y ⟶ S)
    (h' : Z ⟶ S) (w : h' = a ≫ h)
    (M : Sheaf S.smallEtaleTopology A) :
    (((a)^*[A]).mapDerivedCategoryPlusSingleFunctor 0).hom.app _ ≫
      (DerivedCategory.Plus.singleFunctor _ 0).map
        ((upperStarComp A a h h' w).inv.app M) ≫
      (((h')^*[A]).mapDerivedCategoryPlusSingleFunctor 0).inv.app M =
    D+((a)^*[A]).map
        ((((h)^*[A]).mapDerivedCategoryPlusSingleFunctor 0).inv.app M) ≫
      (upperStarCompDerivedPlus A a h h' w).inv.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj M) := by
  apply (cancel_epi ((upperStarCompDerivedPlus A a h h' w).hom.app
    ((DerivedCategory.Plus.singleFunctor _ 0).obj M) ≫
      D+((a)^*[A]).map
        ((((h)^*[A]).mapDerivedCategoryPlusSingleFunctor 0).hom.app M))).1
  simp only [Category.assoc]
  rw [reassoc_of% (comp_single A a h h' w M)]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  simp only [Functor.comp_obj, Category.id_comp, Category.comp_id, Iso.hom_inv_id_app]

private noncomputable def flatten {X Q Y Z : Scheme.{u}}
    (a : Z ⟶ Y) (v : Y ⟶ Q) (q : Q ⟶ X) (av : Z ⟶ Q) (q' : Z ⟶ X)
    (hav : av = a ≫ v) (hq : q' = av ≫ q)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  (upperStarComp AddCommGrpCat.{u + 1} a v av hav).inv.app
      (((q)^*[AddCommGrpCat.{u + 1}]).obj F) ≫
    (upperStarComp AddCommGrpCat.{u + 1} av q q' hq).inv.app F

private lemma flatten_comp_left {X Q Y Y' Z : Scheme.{u}}
    (a : Y' ⟶ Y) (b : Z ⟶ Y') (d : Z ⟶ Y) (hd : d = b ≫ a)
    (v : Y ⟶ Q) (v' : Y' ⟶ Q) (hv : v' = a ≫ v)
    (dv : Z ⟶ Q) (hdv : dv = d ≫ v) (q : Q ⟶ X)
    (q' : Z ⟶ X) (hq : q' = dv ≫ q)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (upperStarComp AddCommGrpCat.{u + 1} b a d hd).hom.app
        (((v)^*[AddCommGrpCat.{u + 1}]).obj (((q)^*[AddCommGrpCat.{u + 1}]).obj F)) ≫
      ((b)^*[AddCommGrpCat.{u + 1}]).map
        ((upperStarComp AddCommGrpCat.{u + 1} a v v' hv).inv.app
          (((q)^*[AddCommGrpCat.{u + 1}]).obj F)) ≫
      flatten b v' q dv q' (by rw [hdv, hd, hv, Category.assoc]) hq F =
    flatten d v q dv q' hdv hq F := by
  dsimp only [flatten]
  rw [upperStarComp_hom_app_map_upperStarComp_inv_app_assoc
    AddCommGrpCat.{u + 1} b a v d v' dv hd hv hdv]
  simp only [Functor.comp_obj, Category.assoc, Iso.hom_inv_id_app, Iso.hom_inv_id_app_assoc,
    Category.comp_id]

private lemma flatten_comp_right {X Q Y Y' Z : Scheme.{u}}
    (a : Y' ⟶ Y) (b : Z ⟶ Y') (d : Z ⟶ Y) (hd : d = b ≫ a)
    (v : Y ⟶ Q) (av : Y' ⟶ Q) (hav : av = a ≫ v)
    (dv : Z ⟶ Q) (hdv : dv = d ≫ v) (q : Q ⟶ X)
    (q' : Y' ⟶ X) (hq : q' = av ≫ q)
    (q'' : Z ⟶ X) (hq' : q'' = dv ≫ q)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (upperStarComp AddCommGrpCat.{u + 1} b a d hd).hom.app
        (((v)^*[AddCommGrpCat.{u + 1}]).obj (((q)^*[AddCommGrpCat.{u + 1}]).obj F)) ≫
      ((b)^*[AddCommGrpCat.{u + 1}]).map (flatten a v q av q' hav hq F) ≫
      (upperStarComp AddCommGrpCat.{u + 1} b q' q''
        (by simp only [hq', hdv, hd, hq, hav, Category.assoc])).inv.app F =
    flatten d v q dv q'' hdv hq' F := by
  dsimp only [flatten]
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [upperStarComp_hom_app_map_upperStarComp_inv_app_assoc
    AddCommGrpCat.{u + 1} b a v d av dv hd hav hdv]
  rw [upperStarComp_hom_app_map_upperStarComp_inv_app_assoc
    AddCommGrpCat.{u + 1} b av q dv q' q''
      (by rw [hdv, hd, hav, Category.assoc]) hq hq']
  simp only [Functor.comp_obj, Category.assoc, Iso.hom_inv_id_app, Iso.hom_inv_id_app_assoc,
    Category.comp_id]

private lemma raw_comp_named {B Y Y' Z : Scheme.{u}}
    (a : Y' ⟶ Y) (b : Z ⟶ Y') (d : Z ⟶ Y) (hd : d = b ≫ a)
    (h : Y ⟶ B) (h' : Y' ⟶ B) (h'' : Z ⟶ B)
    (wa : a ≫ h = h') (wb : b ≫ h' = h'') (wd : d ≫ h = h'') (p : ℕ)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (F' : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1})
    (F'' : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})
    (φa : ((a)^*[AddCommGrpCat.{u + 1}]).obj F ⟶ F')
    (φb : ((b)^*[AddCommGrpCat.{u + 1}]).obj F' ⟶ F'')
    (φd : ((d)^*[AddCommGrpCat.{u + 1}]).obj F ⟶ F'')
    (hφ : φd = (upperStarComp AddCommGrpCat.{u + 1} b a d hd).hom.app F ≫
      ((b)^*[AddCommGrpCat.{u + 1}]).map φa ≫ φb)
    (V : B.Etale) (z : (abelianHigherDirectImageRawPresheaf h p F).obj (op V)) :
    abelianHigherDirectImageRawPullback d h h'' wd p F F'' φd V z =
      abelianHigherDirectImageRawPullback b h' h'' wb p F' F'' φb V
        (abelianHigherDirectImageRawPullback a h h' wa p F F' φa V z) := by
  subst d
  exact abelianHigherDirectImageRawPullback_composition a b (b ≫ a) rfl h h' h''
    wa wb wd p F F' F'' φa φb φd hφ.heq V z

private lemma raw_coefficient_square {B X Q Y Y' Z Z' : Scheme.{u}}
    (l : Y' ⟶ Y) (e : Z ⟶ Y) (e' : Z' ⟶ Y') (t : Z' ⟶ Z)
    (d : Z' ⟶ Y) (hdl : d = e' ≫ l) (hdt : d = t ≫ e)
    (v : Y ⟶ Q) (v' : Y' ⟶ Q) (hv : v' = l ≫ v)
    (ev : Z ⟶ Q) (hev : ev = e ≫ v)
    (dv : Z' ⟶ Q) (hdv : dv = d ≫ v)
    (k : Q ⟶ B) (h : Y ⟶ B) (hh : h = v ≫ k)
    (h' : Y' ⟶ B) (hh' : h' = v' ≫ k)
    (s : Z ⟶ B) (hs : s = e ≫ h)
    (s' : Z' ⟶ B) (hs' : s' = d ≫ h)
    (q : Q ⟶ X) (q' : Z ⟶ X) (hq : q' = ev ≫ q)
    (q'' : Z' ⟶ X) (hq' : q'' = dv ≫ q)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (p : ℕ)
    (V : B.Etale)
    (z : (abelianHigherDirectImageRawPresheaf h p
      (((v)^*[AddCommGrpCat.{u + 1}]).obj (((q)^*[AddCommGrpCat.{u + 1}]).obj F))).obj
        (op V)) :
    abelianHigherDirectImageRawPullback e' h' s'
      (by simp only [hs', hdl, hh', hh, hv, Category.assoc]) p _ _
      (flatten e' v' q dv q'' (by rw [hdv, hdl, hv, Category.assoc]) hq' F) V
      (abelianHigherDirectImageRawPullback l h h'
        (by rw [hh', hh, hv, Category.assoc]) p _ _
        ((upperStarComp AddCommGrpCat.{u + 1} l v v' hv).inv.app
          (((q)^*[AddCommGrpCat.{u + 1}]).obj F)) V z) =
    abelianHigherDirectImageRawPullback t s s'
      (by rw [hs', hdt, hs, Category.assoc]) p _ _
      ((upperStarComp AddCommGrpCat.{u + 1} t q' q''
        (by simp only [hq', hdv, hdt, hq, hev, Category.assoc])).inv.app F) V
      (abelianHigherDirectImageRawPullback e h s hs.symm p _ _
        (flatten e v q ev q' hev hq F) V z) := by
  let φd := flatten d v q dv q'' hdv hq' F
  have hl := flatten_comp_left l e' d hdl v v' hv dv hdv q q'' hq' F
  have ht := flatten_comp_right e t d hdt v ev hev dv hdv q q' hq q'' hq' F
  rw [← raw_comp_named l e' d hdl h h' s' _ _ hs'.symm p _ _ _ _ _ φd hl.symm V z]
  rw [← raw_comp_named e t d hdt h s s' hs.symm _ hs'.symm p _ _ _ _ _ φd ht.symm V z]


end AlgebraicGeometry.Etale

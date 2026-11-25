/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
public import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
public import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparison
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.ComparisonSquarePaths
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.Comparison
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Normalization of the pro-etale comparison-square path under exact derivation

Source: blueprint comparison-square transport, expanded proof step 4.
(blueprint: stage3-proetale-comparison-square-proetale-path-normalization)
-/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

section
variable {A B C P Q R S : Type*}
  [Category A] [Category B] [Category C] [Category P] [Category Q] [Category R] [Category S]
  [Abelian A] [Abelian B] [Abelian C] [Abelian P] [Abelian Q] [Abelian R] [Abelian S]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  [HasDerivedCategory P] [HasDerivedCategory Q] [HasDerivedCategory R] [HasDerivedCategory S]
  (a : A ⥤ B) (b : B ⥤ C) (k : C ⥤ R) (h : B ⥤ Q) (n : A ⥤ P)
  (r : P ⥤ Q) (t : Q ⥤ R) (r' : P ⥤ S) (t' : S ⥤ R)
  [a.Additive] [b.Additive] [k.Additive] [h.Additive] [n.Additive]
  [r.Additive] [t.Additive] [r'.Additive] [t'.Additive]
  [PreservesFiniteLimits a] [PreservesFiniteLimits b] [PreservesFiniteLimits k]
  [PreservesFiniteLimits h] [PreservesFiniteLimits n] [PreservesFiniteLimits r]
  [PreservesFiniteLimits t] [PreservesFiniteLimits r'] [PreservesFiniteLimits t']
  [PreservesFiniteColimits a] [PreservesFiniteColimits b] [PreservesFiniteColimits k]
  [PreservesFiniteColimits h] [PreservesFiniteColimits n] [PreservesFiniteColimits r]
  [PreservesFiniteColimits t] [PreservesFiniteColimits r'] [PreservesFiniteColimits t']

-- Exact derivation respects this three-factor path, with both endpoints normalized.
private theorem exact_path (e : b ⋙ k ≅ h ⋙ t) (c : a ⋙ h ≅ n ⋙ r)
    (s : r ⋙ t ≅ r' ⋙ t') (M : DerivedCategory A) :
    k.mapDerivedCategory.map ((Functor.mapDerivedCategoryCompIso a b).hom.app M) ≫
      (Functor.mapDerivedCategoryCompIso (a ⋙ b) k).hom.app M ≫
      (Functor.mapDerivedCategoryNatIso
        (Functor.isoWhiskerLeft a e ≪≫ Functor.isoWhiskerRight c t ≪≫
          Functor.isoWhiskerLeft n s)).hom.app M ≫
      (Functor.mapDerivedCategoryCompIso n (r' ⋙ t')).inv.app M ≫
      (Functor.mapDerivedCategoryCompIso r' t').inv.app (n.mapDerivedCategory.obj M) =
    ((Functor.mapDerivedCategoryCompIso b k).hom.app (a.mapDerivedCategory.obj M) ≫
      (Functor.mapDerivedCategoryNatIso e).hom.app (a.mapDerivedCategory.obj M) ≫
      (Functor.mapDerivedCategoryCompIso h t).inv.app (a.mapDerivedCategory.obj M)) ≫
    t.mapDerivedCategory.map ((Functor.mapDerivedCategoryCompIso a h).hom.app M ≫
      (Functor.mapDerivedCategoryNatIso c).hom.app M ≫
      (Functor.mapDerivedCategoryCompIso n r).inv.app M) ≫
    (Functor.mapDerivedCategoryCompIso r t).hom.app (n.mapDerivedCategory.obj M) ≫
      (Functor.mapDerivedCategoryNatIso s).hom.app (n.mapDerivedCategory.obj M) ≫
      (Functor.mapDerivedCategoryCompIso r' t').inv.app (n.mapDerivedCategory.obj M) := by
  simp only [Functor.mapDerivedCategoryNatIso_trans, NatTrans.comp_app,
    Functor.map_comp, Category.assoc]
  -- First expose the three whiskered factors and cancel their adjacent comparisons.
  have hL (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
      [PreservesFiniteColimits F] {G G' : B ⥤ R} [G.Additive] [G'.Additive]
      [PreservesFiniteLimits G] [PreservesFiniteColimits G]
      [PreservesFiniteLimits G'] [PreservesFiniteColimits G'] (z : G ≅ G') :
      (Functor.mapDerivedCategoryNatIso (Functor.isoWhiskerLeft F z)).hom.app M =
        (Functor.mapDerivedCategoryCompIso F G).inv.app M ≫
          (Functor.mapDerivedCategoryNatIso z).hom.app (F.mapDerivedCategory.obj M) ≫
          (Functor.mapDerivedCategoryCompIso F G').hom.app M := by
    apply (cancel_mono ((Functor.mapDerivedCategoryCompIso F G').inv.app M)).1
    simpa only [Functor.comp_obj, Category.assoc, Iso.hom_inv_id_app, Category.comp_id,
      NatTrans.comp_app, Functor.whiskerLeft_app] using
      congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerLeft F z) M
  have hR :
      (Functor.mapDerivedCategoryNatIso (Functor.isoWhiskerRight c t)).hom.app M =
        (Functor.mapDerivedCategoryCompIso (a ⋙ h) t).inv.app M ≫
          t.mapDerivedCategory.map ((Functor.mapDerivedCategoryNatIso c).hom.app M) ≫
          (Functor.mapDerivedCategoryCompIso (n ⋙ r) t).hom.app M := by
    apply (cancel_mono ((Functor.mapDerivedCategoryCompIso (n ⋙ r) t).inv.app M)).1
    simpa only [Functor.comp_obj, Category.assoc, Iso.hom_inv_id_app, Category.comp_id,
      NatTrans.comp_app, Functor.whiskerRight_app] using
      congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerRight c t) M
  rw [hL a e, hR]
  have hL' :
      (Functor.mapDerivedCategoryNatIso (Functor.isoWhiskerLeft n s)).hom.app M =
        (Functor.mapDerivedCategoryCompIso n (r ⋙ t)).inv.app M ≫
          (Functor.mapDerivedCategoryNatIso s).hom.app (n.mapDerivedCategory.obj M) ≫
          (Functor.mapDerivedCategoryCompIso n (r' ⋙ t')).hom.app M := by
    apply (cancel_mono ((Functor.mapDerivedCategoryCompIso n (r' ⋙ t')).inv.app M)).1
    simpa only [Functor.comp_obj, Category.assoc, Iso.hom_inv_id_app, Category.comp_id,
      NatTrans.comp_app, Functor.whiskerLeft_app] using
      congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerLeft n s) M
  rw [hL']
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  -- Associativity collects the source, middle and target composition factors.
  have ha (F : A ⥤ B) (G : B ⥤ Q) (H : Q ⥤ R)
      [F.Additive] [G.Additive] [H.Additive]
      [PreservesFiniteLimits F] [PreservesFiniteLimits G] [PreservesFiniteLimits H]
      [PreservesFiniteColimits F] [PreservesFiniteColimits G] [PreservesFiniteColimits H] :
      (Functor.mapDerivedCategoryCompIso F (G ⋙ H)).hom.app M ≫
        (Functor.mapDerivedCategoryCompIso (F ⋙ G) H).inv.app M =
      (Functor.mapDerivedCategoryCompIso G H).inv.app (F.mapDerivedCategory.obj M) ≫
        H.mapDerivedCategory.map ((Functor.mapDerivedCategoryCompIso F G).hom.app M) := by
    have hh := congr_app (Functor.mapDerivedCategoryCompIso_assoc F G H) M
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hh
    apply (cancel_epi ((Functor.mapDerivedCategoryCompIso F (G ⋙ H)).inv.app M)).1
    simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
    rw [hh]
    simp only [Functor.comp_obj, Category.assoc, ← Functor.map_comp,
      Iso.inv_hom_id_app]
    simp only [CategoryTheory.Functor.map_id, Category.comp_id]
  have ha' := congr_app (Functor.mapDerivedCategoryCompIso_assoc a b k) M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at ha'
  have hs :
      k.mapDerivedCategory.map ((Functor.mapDerivedCategoryCompIso a b).hom.app M) ≫
        (Functor.mapDerivedCategoryCompIso (a ⋙ b) k).hom.app M ≫
        (Functor.mapDerivedCategoryCompIso a (b ⋙ k)).inv.app M =
      (Functor.mapDerivedCategoryCompIso b k).hom.app (a.mapDerivedCategory.obj M) := by
    apply (cancel_mono ((Functor.mapDerivedCategoryCompIso b k).inv.app
      (a.mapDerivedCategory.obj M))).1
    simp only [Category.assoc]
    rw [ha']
    simp only [Functor.comp_obj, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp,
      ← Functor.map_comp]
    exact k.mapDerivedCategory.map_id _
  rw [reassoc_of% hs, reassoc_of% (ha a h t)]
  have hn := congr_app (Functor.mapDerivedCategoryCompIso_assoc n r t) M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hn
  have ht :
      (Functor.mapDerivedCategoryCompIso (n ⋙ r) t).hom.app M ≫
        (Functor.mapDerivedCategoryCompIso n (r ⋙ t)).inv.app M =
      t.mapDerivedCategory.map ((Functor.mapDerivedCategoryCompIso n r).inv.app M) ≫
        (Functor.mapDerivedCategoryCompIso r t).hom.app (n.mapDerivedCategory.obj M) := by
    apply (cancel_mono ((Functor.mapDerivedCategoryCompIso r t).inv.app
      (n.mapDerivedCategory.obj M))).1
    simp only [Category.assoc]
    rw [hn]
    simp only [Functor.comp_obj, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp,
      Category.comp_id]
  rw [reassoc_of% ht]
end

attribute [local implicit_reducible] upperStar Etale.upperStar comparisonUpperStar

-- Equality transport commutes with exact derivation and the exactness comparison.
private theorem derive_transport
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} {f g : X ⟶ Y} (w : f = g)
    (N : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))) :
    (Functor.mapDerivedCategoryNatIso
      (eqToIso (congrArg (upperStar (ModuleCat.{u + 1} Λ)) w))).hom.app N =
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) f).inv.app N ≫
        (leftDerivedUpperStarCongr (ModuleCat.{u + 1} Λ) w).hom.app N ≫
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) g).hom.app N := by
  subst g
  simp only [leftDerivedUpperStarCongr_rfl, Iso.refl_hom, NatTrans.id_app,
    Category.id_comp, Iso.inv_hom_id_app]
  change (Functor.mapDerivedCategoryNatIso (Iso.refl _)).hom.app N = _
  rw [Functor.mapDerivedCategoryNatIso_refl]
  rfl

-- Normalize the derived square independently of the edge comparison maps.
private theorem square_exact
    (Λ : Type (u + 1)) [CommRing Λ]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' f' f g)
    (cs : ChosenCartesianSquare g' f' f g)
    (N : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))) :
    (leftDerivedUpperStarSquareIso (ModuleCat.{u + 1} Λ) sq).hom.app N =
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) f').hom.app
          (L(upperStar (ModuleCat.{u + 1} Λ) g).obj N) ≫
      D(upperStar (ModuleCat.{u + 1} Λ) f').map
        ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) g).hom.app N) ≫
      (Functor.mapDerivedCategoryCompIso (upperStar (ModuleCat.{u + 1} Λ) g)
        (upperStar (ModuleCat.{u + 1} Λ) f')).hom.app N ≫
      (Functor.mapDerivedCategoryNatIso
        (F := upperStar (ModuleCat.{u + 1} Λ) g ⋙ upperStar (ModuleCat.{u + 1} Λ) f')
        (G := upperStar (ModuleCat.{u + 1} Λ) f ⋙ upperStar (ModuleCat.{u + 1} Λ) g')
        (proEtaleComparisonSquare (ModuleCat.{u + 1} Λ) cs)).hom.app N ≫
      (Functor.mapDerivedCategoryCompIso (upperStar (ModuleCat.{u + 1} Λ) f)
        (upperStar (ModuleCat.{u + 1} Λ) g')).inv.app N ≫
      D(upperStar (ModuleCat.{u + 1} Λ) g').map
        ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) f).inv.app N) ≫
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) g').inv.app
        (L(upperStar (ModuleCat.{u + 1} Λ) f).obj N) := by
  simp only [leftDerivedUpperStarSquareIso, leftDerivedUpperStarComp,
    Functor.leftDerivedFunctorNatIso, Functor.leftDerivedFunctorCompIso,
    Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.assoc, Iso.inv_hom_id_app_assoc]
  simp only [Iso.symm_inv, Iso.inv_hom_id_app_assoc,
    leftDerivedUpperStarIsoMapDerivedCategory]
  have ht := derive_transport Λ cs.w.symm N
  simp only [leftDerivedUpperStarIsoMapDerivedCategory] at ht
  rw [reassoc_of% ht.symm]
  have hs : proEtaleComparisonSquare (ModuleCat.{u + 1} Λ) cs =
      (upperStarComp (ModuleCat.{u + 1} Λ) f' g).symm ≪≫
        eqToIso (congrArg (upperStar (ModuleCat.{u + 1} Λ)) cs.w.symm) ≪≫
          upperStarComp (ModuleCat.{u + 1} Λ) g' f := by
    rfl
  rw [hs]
  simp only [Functor.mapDerivedCategoryNatIso_trans, Functor.mapDerivedCategoryNatIso_symm,
    NatTrans.comp_app, Category.assoc]

private theorem normalized_path
    (Λ : Type (u + 1)) [CommRing Λ]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' f' f g)
    (cs : ChosenCartesianSquare g' f' f g)
    (M : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    D(ν^*(X')[ModuleCat.{u + 1} Λ]).map
        ((Functor.mapDerivedCategoryCompIso (Etale.upperStar (ModuleCat.{u + 1} Λ) g)
          (Etale.upperStar (ModuleCat.{u + 1} Λ) f')).hom.app M.obj) ≫
      (Functor.mapDerivedCategoryCompIso
        (Etale.upperStar (ModuleCat.{u + 1} Λ) g ⋙
          Etale.upperStar (ModuleCat.{u + 1} Λ) f')
        ν^*(X')[ModuleCat.{u + 1} Λ]).hom.app M.obj ≫
      (Functor.mapDerivedCategoryNatIso
        (Functor.isoWhiskerLeft (Etale.upperStar (ModuleCat.{u + 1} Λ) g)
            (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f').symm ≪≫
          Functor.isoWhiskerRight
            (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) g).symm
            (upperStar (ModuleCat.{u + 1} Λ) f') ≪≫
          Functor.isoWhiskerLeft ν^*(Y)[ModuleCat.{u + 1} Λ]
            (show upperStar (ModuleCat.{u + 1} Λ) g ⋙ upperStar (ModuleCat.{u + 1} Λ) f' ≅
                upperStar (ModuleCat.{u + 1} Λ) f ⋙ upperStar (ModuleCat.{u + 1} Λ) g' from
              proEtaleComparisonSquare (ModuleCat.{u + 1} Λ) cs))).hom.app M.obj ≫
      (Functor.mapDerivedCategoryCompIso ν^*(Y)[ModuleCat.{u + 1} Λ]
        (upperStar (ModuleCat.{u + 1} Λ) f ⋙ upperStar (ModuleCat.{u + 1} Λ) g')).inv.app
          M.obj ≫
      (Functor.mapDerivedCategoryCompIso (upperStar (ModuleCat.{u + 1} Λ) f)
        (upperStar (ModuleCat.{u + 1} Λ) g')).inv.app
          (D(ν^*(Y)[ModuleCat.{u + 1} Λ]).obj M.obj) ≫
      D(upperStar (ModuleCat.{u + 1} Λ) g').map
        ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) f).inv.app
          (D(ν^*(Y)[ModuleCat.{u + 1} Λ]).obj M.obj)) ≫
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) g').inv.app
        (L(upperStar (ModuleCat.{u + 1} Λ) f).obj
          (D(ν^*(Y)[ModuleCat.{u + 1} Λ]).obj M.obj)) =
    (leftDerivedUpperStarComparisonIso f' Λ).hom.app
          (D+(Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj M) ≫
      L(upperStar (ModuleCat.{u + 1} Λ) f').map
        ((leftDerivedUpperStarComparisonIso g Λ).hom.app M) ≫
      (leftDerivedUpperStarSquareIso (ModuleCat.{u + 1} Λ) sq).hom.app
        (D(ν^*(Y)[ModuleCat.{u + 1} Λ]).obj M.obj) := by
  have hp := exact_path
    (Etale.upperStar (ModuleCat.{u + 1} Λ) g)
    (Etale.upperStar (ModuleCat.{u + 1} Λ) f') ν^*(X')[ModuleCat.{u + 1} Λ]
    ν^*(Y')[ModuleCat.{u + 1} Λ] ν^*(Y)[ModuleCat.{u + 1} Λ]
    (upperStar (ModuleCat.{u + 1} Λ) g) (upperStar (ModuleCat.{u + 1} Λ) f')
    (upperStar (ModuleCat.{u + 1} Λ) f) (upperStar (ModuleCat.{u + 1} Λ) g')
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f').symm
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) g).symm
    (proEtaleComparisonSquare (ModuleCat.{u + 1} Λ) cs) M.obj
  rw [reassoc_of% hp]
  rw [square_exact Λ sq cs]
  simp only [leftDerivedUpperStarComparisonIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.mapDerivedCategoryPlusCompatibility, Iso.refl_hom, NatTrans.id_app,
    CategoryTheory.Functor.map_id, Category.assoc]
  dsimp only [Functor.comp_obj, ObjectProperty.ι_obj, Functor.mapDerivedCategoryPlus,
    ObjectProperty.lift_obj_obj]
  simp only [Category.id_comp]
  rw [← NatTrans.naturality_assoc]
  simp only [Iso.inv_hom_id_app_assoc, Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp]

/-- Exact derivation of the ordinary ProEtale path, with the common source and target
composition factors. This identity concerns one path and assumes no square coherence.
The heterogeneous equality retains the two endpoint presentations; these endpoints
are definitionally equal. It avoids unfolding the derived functor constructions
when joining the two normalization identities.
Source: blueprint `stage3-proetale-comparison-square`, proof step 4; Stacks, Tag 0B65.
(blueprint: stage3-proetale-comparison-square-proetale-path-normalization)

Proof: write C(F,G) for mapDerivedCategoryCompIso F G and J(f) for
leftDerivedUpperStarIsoMapDerivedCategory at f. Expand the ordinary path as the
comparison at f' whiskered by g_et, the comparison at g whiskered by f'_proet, and
the pro-etale square whiskered by nu_Y. Apply mapDerivedCategoryNatIso_trans and its
left/right whiskering equations. The associativity equation for C collects the
source factors into comparisonSquareSourceIso and the target factors into the exact
part of comparisonSquareTargetIso; all intermediate C-inverse pairs cancel. This
leaves the two exact derived edge comparisons followed by the derived ordinary
pro-etale square.

Expand leftDerivedUpperStarComparisonIso at f' and g. Its ordinary comparison is
definitionally comparisonCoefficientPullbackIso, and its final factor is J.inv.
Naturality of J(f').inv moves the factor for f' past the exact derived comparison
at g. Thus the first two displayed arrows give the same exact derived edge path,
followed by the two inverse J factors for g and f'. Expand
leftDerivedUpperStarSquareIso into its inverse composition comparison, equality
transport, and forward composition comparison. In leftDerivedFunctorNatIso and
leftDerivedFunctorCompIso the J factor for a composite cancels with its inverse.
The remaining composition factors are C conjugated by the individual J factors.
Equality induction for leftDerivedUpperStarCongr identifies the middle transport
with the derived transport in proEtaleComparisonSquare. Cancel the J factors for
g and f' against those from the edge path. The surviving inverse J factors for
f and g' are exactly the final factors of comparisonSquareTargetIso. Evaluate at
M.obj and associate the composites. Restriction to D+ only contributes the identity
mapDerivedCategoryPlusCompatibility on the source edges; no etale square identity
or coherence hypothesis is used. Identity edges and zero input obey the same
naturality and cancellation equations. -/
theorem comparisonSquareProEtalePath_normalization
    (Λ : Type (u + 1)) [CommRing Λ]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    (M : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    HEq
      (comparisonSquareDerivedPath Λ g' f' f g (comparisonSquareProEtalePath Λ
        { toCommSq := sq.toCommSq, isoPullback := sq.isoPullback,
          hom_fst := sq.isoPullback_hom_fst, hom_snd := sq.isoPullback_hom_snd }) M)
      ((leftDerivedUpperStarComparisonIso f' Λ).hom.app
            (D+(Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj M) ≫
          L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) f').map
            ((leftDerivedUpperStarComparisonIso g Λ).hom.app M) ≫
          (leftDerivedUpperStarSquareIso (ModuleCat.{u + 1} Λ) sq.toCommSq).hom.app
            ((DerivedCategory.Plus.ι ⋙ D(ν^*(Y)[ModuleCat.{u + 1} Λ])).obj M)) := by
  let cs : ChosenCartesianSquare g' f' f g :=
    { toCommSq := sq.toCommSq, isoPullback := sq.isoPullback,
      hom_fst := sq.isoPullback_hom_fst, hom_snd := sq.isoPullback_hom_snd }
  convert heq_of_eq (normalized_path Λ sq.toCommSq cs M) using 1 <;> try rfl
  have edge_eq {T S : Scheme.{u}} (a : T ⟶ S) :
      comparisonCoefficientPullbackIso (ModuleCat.{u + 1} Λ) a =
        (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) a).symm := by
    rfl
  simp only [comparisonSquareDerivedPath, comparisonSquareSourceIso,
    comparisonSquareTargetIso, comparisonSquareProEtalePath, comparisonSquareProEtalePathOfData,
    comparisonSquareData, Iso.trans_inv, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, edge_eq, Category.assoc]
  rfl

end AlgebraicGeometry.ProEtale

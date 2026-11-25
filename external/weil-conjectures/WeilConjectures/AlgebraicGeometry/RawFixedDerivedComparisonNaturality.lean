/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RawFixedDerivedComparison
public import WeilConjectures.AlgebraicGeometry.RawRestrictedDerivedComparisonPullback
public import WeilConjectures.AlgebraicGeometry.EtaleComplexPullbackTransport
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars
import all WeilConjectures.AlgebraicGeometry.RestrictedDerivedSectionsShiftTransport
import WeilConjectures.AlgebraicGeometry.RestrictedDerivedSectionPullbackCommShift

/-! # Naturality of fixed-coefficient raw evaluation

Source: Stacks Project, Tags 03Q8, 0D6F and 0GIT.
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

attribute [local irreducible] upperStar upperStarCompDerivedPlus
  rawFixedDerivedComparison presentationDerivedMap

private noncomputable abbrev Ciso {X Y T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ T) (h : X ⟶ T := f ≫ g)
    (hh : h = f ≫ g := by cat_disch) :=
  Functor.mapDerivedCategoryTriangleIso
    (upperStarComp AddCommGrpCat.{u + 1} f g h hh)
set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 2048 in
private theorem comp_assoc {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
    (K : DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    (Ciso f (g ≫ h)).hom.app K ≫
      (D((f)^*[AddCommGrpCat.{u + 1}])).map ((Ciso g h).hom.app K) =
    (Ciso (f ≫ g) h (f ≫ g ≫ h) (Category.assoc f g h).symm).hom.app K ≫
      (Ciso f g).hom.app ((D((h)^*[AddCommGrpCat.{u + 1}])).obj K) := by
  let F := upperStar AddCommGrpCat.{u + 1} h
  let G := upperStar AddCommGrpCat.{u + 1} g
  let H := upperStar AddCommGrpCat.{u + 1} f
  let a := upperStarComp AddCommGrpCat.{u + 1} f (g ≫ h)
  let b := upperStarComp AddCommGrpCat.{u + 1} g h
  let c := upperStarComp AddCommGrpCat.{u + 1} (f ≫ g) h
    (f ≫ g ≫ h) (Category.assoc f g h).symm
  let d := upperStarComp AddCommGrpCat.{u + 1} f g
  have hu := upperStarComp_assoc AddCommGrpCat.{u + 1} f g h
  have hassoc : F.associator G H = Iso.refl _ := by ext; rfl
  change a ≪≫ Functor.isoWhiskerRight b H ≪≫ F.associator G H =
    c ≪≫ Functor.isoWhiskerLeft F d at hu
  rw [hassoc, Iso.trans_refl] at hu
  have hm := congrArg (fun e ↦ (Functor.mapDerivedCategoryNatIso e).hom.app K) hu
  simp only [Functor.mapDerivedCategoryNatIso_trans, NatTrans.comp_app] at hm
  have hwr := congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerRight b H) K
  have hwl := congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerLeft F d) K
  have ha := congr_app (Functor.mapDerivedCategoryCompIso_assoc F G H) K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    at hwr hwl ha
  simp only [Ciso, Functor.mapDerivedCategoryTriangleIso, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hwr, ← reassoc_of% hwl]
  rw [← ha, reassoc_of% hm]
set_option backward.isDefEq.respectTransparency false in
private theorem comp_assoc_named {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
    (fg : X ⟶ Z) (hfg : fg = f ≫ g) (gh : Y ⟶ T) (hgh : gh = g ≫ h)
    (fgh : X ⟶ T) (hfgh : fgh = f ≫ gh)
    (K : DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    (Ciso f gh fgh hfgh).hom.app K ≫
      (D((f)^*[AddCommGrpCat.{u + 1}])).map ((Ciso g h gh hgh).hom.app K) =
    (Ciso fg h fgh (by rw [hfgh, hfg, hgh, Category.assoc])).hom.app K ≫
      (Ciso f g fg hfg).hom.app ((D((h)^*[AddCommGrpCat.{u + 1}])).obj K) := by
  subst fg
  subst gh
  subst fgh
  exact comp_assoc f g h K
set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 2048 in
private theorem coefficient_square {X X' Y Y' T : Scheme.{u}}
    (s : X' ⟶ X) (r : X ⟶ Y) (r' : X' ⟶ Y') (a : Y' ⟶ Y)
    (hw : r' ≫ a = s ≫ r) (g : Y ⟶ T) (g' : Y' ⟶ T) (wg : g' = a ≫ g)
    (K : DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    (D((s)^*[AddCommGrpCat.{u + 1}])).map ((Ciso r g).inv.app K) ≫
      (Ciso s (r ≫ g) (r' ≫ g') (by simp only [wg, ← Category.assoc, hw])).inv.app K =
    (Ciso s r).inv.app ((D((g)^*[AddCommGrpCat.{u + 1}])).obj K) ≫
      (Ciso r' a (s ≫ r) hw.symm).hom.app ((D((g)^*[AddCommGrpCat.{u + 1}])).obj K) ≫
      (D((r')^*[AddCommGrpCat.{u + 1}])).map ((Ciso a g g' wg).inv.app K) ≫
      (Ciso r' g').inv.app K := by
  have h₁ := comp_assoc_named s r g (s ≫ r) rfl (r ≫ g) rfl
    (r' ≫ g') (by simp only [wg, ← Category.assoc, hw]) K
  have h₂ := comp_assoc_named r' a g (s ≫ r) hw.symm g' wg (r' ≫ g') rfl K
  apply (cancel_epi ((Ciso s (r ≫ g) (r' ≫ g')
    (by simp only [wg, ← Category.assoc, hw])).hom.app K ≫
    (D((s)^*[AddCommGrpCat.{u + 1}])).map ((Ciso r g).hom.app K))).mp
  apply (cancel_mono ((Ciso r' g').hom.app K ≫
    (D((r')^*[AddCommGrpCat.{u + 1}])).map ((Ciso a g g' wg).hom.app K))).mp
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [reassoc_of% h₁]
  simp only [Iso.hom_inv_id_app_assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  exact h₂

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 2048 in
private theorem restriction_hom_eq {B Y Y' : Scheme.{u}}
    (a : Y' ⟶ Y) (h : Y ⟶ B) (h' : Y' ⟶ B) (w : a ≫ h = h') (U : B.Etale)
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    (RawRestrictedComparison.derivedRestrictionIso a h h' w U).hom.app K =
      (Ciso (rawAffineRestrictedMap a h h' w U) (pullback.snd U.hom h)).inv.app K ≫
        (Ciso (pullback.snd U.hom h') a
          (rawAffineRestrictedMap a h h' w U ≫ pullback.snd U.hom h)
          (by simp [rawAffineRestrictedMap])).hom.app K := by
  simp only [RawRestrictedComparison.derivedRestrictionIso, Ciso,
    Functor.mapDerivedCategoryTriangleIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    NatTrans.comp_app, Functor.mapDerivedCategoryNatIso_trans,
    Functor.mapDerivedCategoryNatIso_symm, Category.assoc]

set_option maxRecDepth 2048 in
set_option backward.isDefEq.respectTransparency false in
-- Comparing the two canonical section functors requires substantial type reduction.
private theorem shift_iso_hom {B Y : Scheme.{u}} (h : Y ⟶ B) (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (U : B.Etale) :
    (RawRestrictedComparison.derivedShiftIso h q K U).hom =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0).map
        (((RawRestrictedComparison.sectionsFunctor
          ((MorphismProperty.Over.pullback @Etale ⊤ h).obj U)).commShiftIso q).hom.app K) ≫
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0).shiftIso q 0 q
        (add_zero q)).hom.app ((RawRestrictedComparison.sectionsFunctor
          ((MorphismProperty.Over.pullback @Etale ⊤ h).obj U)).obj K) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
-- Comparing the two canonical section functors requires substantial type reduction.
set_option maxRecDepth 2048 in
private theorem raw_pullback_homology {B Y Y' : Scheme.{u}}
    (a : Y' ⟶ Y) (h : Y ⟶ B) (h' : Y' ⟶ B) (w : a ≫ h = h')
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (K' : DerivedCategory.Plus (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (φ : (D+((a)^*[AddCommGrpCat.{u + 1}])).obj K ⟶ K')
    (q : ℤ) (U : B.Etale) :
    rawRestrictedDerivedCohomologyPullback a h h' w K K' φ q U =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} q).map
        ((RawRestrictedComparison.restrictedDerivedSectionPullback a h h' w U).app K ≫
          (RawRestrictedComparison.sectionsFunctor
            ((MorphismProperty.Over.pullback @Etale ⊤ h').obj U)).map φ) := by
  let T := RawRestrictedComparison.sectionsFunctor
    ((MorphismProperty.Over.pullback @Etale ⊤ h).obj U)
  let T' := RawRestrictedComparison.sectionsFunctor
    ((MorphismProperty.Over.pullback @Etale ⊤ h').obj U)
  let L := D+((a)^*[AddCommGrpCat.{u + 1}])
  let τ := RawRestrictedComparison.restrictedDerivedSectionPullback a h h' w U
  have := RawRestrictedComparison.restrictedDerivedSectionPullback_commShift a h h' w U
  have ht := RawRestrictedComparison.transport_homology T T' L τ
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0)
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} q) q
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0).shiftIso q 0 q
      (add_zero q)).hom φ (Iso.refl _) (Iso.refl _)
  dsimp only [T, T', L, τ] at ht
  simp only [Iso.refl_hom, Iso.refl_inv, Category.id_comp, Category.comp_id] at ht
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id] at ht
  simp only [Category.comp_id, Category.id_comp] at ht
  apply (cancel_epi (RawRestrictedComparison.derivedShiftIso h q K U).hom).mp
  rw [rawRestrictedDerivedCohomologyPullback_eq]
  simp only [Iso.hom_inv_id_assoc]
  change (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0).map
      (τ.app (K⟦q⟧)) ≫
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0).map
      (T'.map ((L.commShiftIso q).hom.app K ≫ (shiftFunctor _ q).map φ)) ≫
    (RawRestrictedComparison.derivedShiftIso h' q K' U).hom =
    (RawRestrictedComparison.derivedShiftIso h q K U).hom ≫
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} q).map
        (τ.app K ≫ T'.map φ)
  rw [shift_iso_hom, shift_iso_hom]
  simpa only [Category.assoc] using ht

set_option backward.isDefEq.respectTransparency false in
private theorem fixed_section_square {B T Y Y' : Scheme.{u}}
    (a : Y' ⟶ Y) (h : Y ⟶ B) (h' : Y' ⟶ B) (w : a ≫ h = h')
    (g : Y ⟶ T) (g' : Y' ⟶ T) (wg : g' = a ≫ g)
    (K : DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})) (U : B.Etale) :
    let s := rawAffineRestrictedMap a h h' w U
    let r := pullback.snd U.hom h
    let r' := pullback.snd U.hom h'
    let R := rightDerivedGlobalSections AddCommGrpCat.{u + 1} (pullback U.hom h)
    let R' := rightDerivedGlobalSections AddCommGrpCat.{u + 1} (pullback U.hom h')
    R.map ((Ciso r g).inv.app K) ≫
      (RawRestrictedComparison.derivedSectionPullback s).app
        ((D(((r ≫ g))^*[AddCommGrpCat.{u + 1}])).obj K) ≫
      R'.map ((Ciso s (r ≫ g) (r' ≫ g')
        (by simp [s, r, r', rawAffineRestrictedMap, wg, Category.assoc])).inv.app K) =
    ((RawRestrictedComparison.derivedSectionPullback s).app
        ((D((r)^*[AddCommGrpCat.{u + 1}])).obj
          ((D((g)^*[AddCommGrpCat.{u + 1}])).obj K)) ≫
      R'.map ((RawRestrictedComparison.derivedRestrictionIso a h h' w U).hom.app
        ((D((g)^*[AddCommGrpCat.{u + 1}])).obj K))) ≫
      R'.map ((D((r')^*[AddCommGrpCat.{u + 1}])).map
        ((Ciso a g g' wg).inv.app K)) ≫ R'.map ((Ciso r' g').inv.app K) := by
  dsimp only
  rw [reassoc_of% (RawRestrictedComparison.derivedSectionPullback
    (rawAffineRestrictedMap a h h' w U)).naturality
      ((Ciso (pullback.snd U.hom h) g).inv.app K)]
  simp only [Category.assoc, ← Functor.map_comp]
  congr 2
  rw [restriction_hom_eq]
  simp only [Category.assoc]
  exact coefficient_square (rawAffineRestrictedMap a h h' w U)
    (pullback.snd U.hom h) (pullback.snd U.hom h') a
    (by simp [rawAffineRestrictedMap]) g g' wg K

set_option backward.isDefEq.respectTransparency false in
private theorem plus_comp_inv {X Y T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ T) (h : X ⟶ T) (hh : h = f ≫ g)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    DerivedCategory.Plus.ι.map
      ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1} f g h hh).inv.app K) =
    (Ciso f g h hh).inv.app K.obj := by
  have he : DerivedCategory.Plus.ι.map
      ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1} f g h hh).hom.app K) =
      (Ciso f g h hh).hom.app K.obj := by
    simp only [upperStarCompDerivedPlus, Ciso, Functor.mapDerivedCategoryTriangleIso,
      Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp,
      Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app,
      Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app, ObjectProperty.ι_obj]
  have hi : (DerivedCategory.Plus.ι.mapIso
      ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1} f g h hh).app K)) =
      (Ciso f g h hh).app K.obj := Iso.ext he
  exact congrArg Iso.inv hi

set_option backward.isDefEq.respectTransparency false in
private theorem presentation_eq {X Y T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ T) (h : X ⟶ T) (hh : h = f ≫ g)
    (K : DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})) (q : ℤ) :
    presentationDerivedMap f g h hh K q =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} q).map
        ((RawRestrictedComparison.derivedSectionPullback f).app
            ((D((g)^*[AddCommGrpCat.{u + 1}])).obj K) ≫
          (rightDerivedGlobalSections AddCommGrpCat.{u + 1} X).map
            ((Ciso f g h hh).inv.app K)) := by
  simp only [presentationDerivedMap, RawRestrictedComparison.derivedSectionPullback,
    rightDerivedLowerStarCompRightDerivedGlobalSectionsIso, lowerStarCompGlobalSectionsIso,
    cohomology, Functor.comp_map, Functor.map_comp, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.assoc, Ciso,
    Functor.mapDerivedCategoryTriangleIso]

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 2048 in
private theorem fixed_cohomology_square {B T Y Y' : Scheme.{u}}
    (a : Y' ⟶ Y) (h : Y ⟶ B) (h' : Y' ⟶ B) (w : a ≫ h = h')
    (g : Y ⟶ T) (g' : Y' ⟶ T) (wg : g' = a ≫ g)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (q : ℤ) (U : B.Etale) :
    (cohomology AddCommGrpCat.{u + 1} (pullback U.hom h) q).map
        ((Ciso (pullback.snd U.hom h) g).inv.app K.obj) ≫
      presentationDerivedMap (rawAffineRestrictedMap a h h' w U)
        (pullback.snd U.hom h ≫ g) (pullback.snd U.hom h' ≫ g')
        (by simp [rawAffineRestrictedMap, wg, Category.assoc]) K.obj q =
    rawRestrictedDerivedCohomologyPullback a h h' w _ _
      ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1} a g g' wg).inv.app K) q U ≫
      (cohomology AddCommGrpCat.{u + 1} (pullback U.hom h') q).map
        ((Ciso (pullback.snd U.hom h') g').inv.app K.obj) := by
  rw [raw_pullback_homology, presentation_eq]
  simp only [cohomology, Functor.comp_map, ← Functor.map_comp]
  apply congrArg ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} q).map)
  simp only [RawRestrictedComparison.restrictedDerivedSectionPullback,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc]
  change
    (rightDerivedGlobalSections AddCommGrpCat.{u + 1} (pullback U.hom h)).map
      ((Ciso (pullback.snd U.hom h) g).inv.app K.obj) ≫
      (RawRestrictedComparison.derivedSectionPullback
        (rawAffineRestrictedMap a h h' w U)).app
          ((D(((pullback.snd U.hom h ≫ g))^*[AddCommGrpCat.{u + 1}])).obj K.obj) ≫
      (rightDerivedGlobalSections AddCommGrpCat.{u + 1} (pullback U.hom h')).map
        ((Ciso (rawAffineRestrictedMap a h h' w U) (pullback.snd U.hom h ≫ g)
          (pullback.snd U.hom h' ≫ g')
          (by simp [rawAffineRestrictedMap, wg, Category.assoc])).inv.app K.obj) =
    (RawRestrictedComparison.derivedSectionPullback
      (rawAffineRestrictedMap a h h' w U)).app
        ((D((pullback.snd U.hom h)^*[AddCommGrpCat.{u + 1}])).obj
          ((D((g)^*[AddCommGrpCat.{u + 1}])).obj K.obj)) ≫
      (rightDerivedGlobalSections AddCommGrpCat.{u + 1} (pullback U.hom h')).map
        ((RawRestrictedComparison.derivedRestrictionIso a h h' w U).hom.app
          ((D((g)^*[AddCommGrpCat.{u + 1}])).obj K.obj)) ≫
      (rightDerivedGlobalSections AddCommGrpCat.{u + 1} (pullback U.hom h')).map
        ((D((pullback.snd U.hom h')^*[AddCommGrpCat.{u + 1}])).map
          (DerivedCategory.Plus.ι.map
            ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1} a g g' wg).inv.app K))) ≫
      (rightDerivedGlobalSections AddCommGrpCat.{u + 1} (pullback U.hom h')).map
        ((Ciso (pullback.snd U.hom h') g').inv.app K.obj)
  rw [plus_comp_inv]
  simpa only [Category.assoc] using fixed_section_square a h h' w g g' wg K.obj U

/-- Raw evaluation intertwines triangle pullback with canonical cohomology pullback.
Source: Stacks Project, Tag 03Q8, restriction in Tag 0D6F, and the canonical maps of 0GIT.
(blueprint: lem-sc-raw-fixed-derived-comparison-naturality).

Proof: Apply rawRestrictedDerivedComparison_pullback to the coefficient morphism
which is the inverse derived inverse-image composition comparison. The restricted
section pullback commutes with shifts. Thus its conjugate by the two derivedShiftIso
maps is homology in degree q of its unshifted map. Expand that map: it is the
adjunction unit for U times_B a followed by Leray and the restriction composition
comparison. Naturality moves the coefficient composition comparison past the unit
and Leray. Inverse-image associativity, applied to the two projections and a,g,
cancels the restriction comparison with the two coefficient comparisons. What
remains is exactly presentationDerivedMap. All steps are identities of natural
transformations, and cover empty U, zero K, identity a and every integer q. No
limit, affine or qcqs hypothesis is involved. -/
theorem rawFixedDerivedComparison_naturality {B T Y Y' : Scheme.{u}}
    (a : Y' ⟶ Y) (h : Y ⟶ B) (h' : Y' ⟶ B) (w : a ≫ h = h')
    (g : Y ⟶ T) (g' : Y' ⟶ T) (wg : g' = a ≫ g)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (q : ℤ) (U : B.Etale)
    (z : (DerivedCategory.Plus.singleFunctor _ 0).obj
      (((h)^*[AddCommGrpCat.{u + 1}]).obj ((abelianComparisonFree B).obj U)) ⟶
      ((D+((g)^*[AddCommGrpCat.{u + 1}])).obj K)⟦q⟧) :
    presentationDerivedMap (rawAffineRestrictedMap a h h' w U)
        (pullback.snd U.hom h ≫ g) (pullback.snd U.hom h' ≫ g')
        (by simp [rawAffineRestrictedMap, wg, Category.assoc]) K.obj q
        (rawFixedDerivedComparison h g K q U z) =
      rawFixedDerivedComparison h' g' K q U
        (rawRestrictedDerivedPullback a h h' w _ _
          ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1} a g g' wg).inv.app K)
          q U z) := by
  have hs := ConcreteCategory.congr_hom (fixed_cohomology_square a h h' w g g' wg K q U)
    (rawRestrictedDerivedComparison h q ((D+((g)^*[AddCommGrpCat.{u + 1}])).obj K) U z)
  simp only [ConcreteCategory.comp_apply] at hs
  erw [rawRestrictedDerivedComparison_pullback] at hs
  simp only [rawFixedDerivedComparison, ConcreteCategory.comp_apply]
  simp only [Ciso, Functor.mapDerivedCategoryTriangleIso] at hs
  exact hs

end AlgebraicGeometry.Etale

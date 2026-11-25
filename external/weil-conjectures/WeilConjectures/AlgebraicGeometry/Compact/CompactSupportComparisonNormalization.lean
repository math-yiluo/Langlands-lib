/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalCompactSupportSiteComparison
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonClassAdjunction
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Agreement of the two specified compact-support site comparisons

Source: blueprint thm-sf-ambient-adjoint-class.proof.md, normalized Hom chain.
(blueprint: lem-coef-compact-support-comparison-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.ProEtale

set_option backward.isDefEq.respectTransparency false in
/-- The comparison used in the specified exceptional Hom chain is the canonical
proper/open compact-support comparison.

Source: blueprint thm-sf-ambient-adjoint-class.proof.md, four-factor Hom chain,
and lem-coef-finite-dualizing.proof.md, paragraph 3
(blueprint: lem-coef-compact-support-comparison-normalization).

Proof: expand both comparisons into the exact open extension comparison followed
by the canonical proper direct-image counit mate. The open comparison on D+ is the
restriction of the termwise comparison on the unbounded category. Naturality of
rightDerivedFunctorPlusCompatibility moves this identification through the proper
factor. Compatibility of mapDerivedCategoryPlus with composition identifies the
remaining inclusion comparisons. Thus both components are the same proper mate
composed with the same exact open comparison. Componentwise equality gives the
natural-isomorphism equality. This also applies to identity-open compactifications
and to the empty source; no new adjunction is chosen. -/
theorem compactSupportComparisonNormalization
    (R : Type (u + 1)) [CommRing R] [Finite R]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    fixedCompactSupportComparisonIso R c = compactSupportSiteComparison R c := by
  apply Iso.ext
  ext K
  let C := ModuleCat.{u + 1} R
  let T := comparisonUpperStar C X
  let U := comparisonUpperStar C c.Z
  let V := comparisonUpperStar C Y
  let L := Etale.openImmersionLowerShriek C c.i
  let L' := openImmersionLowerShriek C c.i
  let G := lowerStar C c.g
  let e := openImmersionLowerShriekComparisonUpperStarIso C c.i
  let d := Functor.mapDerivedCategoryCompIso T L' ≪≫
    Functor.mapDerivedCategoryNatIso e.symm ≪≫ (Functor.mapDerivedCategoryCompIso L U).symm
  let dplus := properOpenSiteExtensionIso R c.i
  have hc : _root_.DerivedCategory.Plus.ι.map
      ((Functor.mapDerivedCategoryPlusCompIso T L').inv.app K) =
      (Functor.mapDerivedCategoryCompIso T L').hom.app K.obj := by
    have h : _root_.DerivedCategory.Plus.ι.mapIso
        ((Functor.mapDerivedCategoryPlusCompIso T L').app K) =
        (Functor.mapDerivedCategoryCompIso T L').symm.app K.obj :=
      Iso.ext (Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app T L' K)
    exact congrArg Iso.inv h
  have hn : _root_.DerivedCategory.Plus.ι.map
      ((Functor.mapDerivedCategoryPlusNatIso e).inv.app K) =
      (Functor.mapDerivedCategoryNatIso e).inv.app K.obj := by
    have h : _root_.DerivedCategory.Plus.ι.mapIso
        ((Functor.mapDerivedCategoryPlusNatIso e).app K) =
        (Functor.mapDerivedCategoryNatIso e).app K.obj :=
      Iso.ext (Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app e K)
    exact congrArg Iso.inv h
  have hd : _root_.DerivedCategory.Plus.ι.map (dplus.inv.app K) = d.hom.app K.obj := by
    dsimp only [dplus, properOpenSiteExtensionIso, d, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app]
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, hc, hn,
      Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app]
    rw [Functor.mapDerivedCategoryNatIso_symm]
    rw [Category.assoc]
    rfl
  have hcore := G.rightDerivedFunctorPlusCompatibility.inv.naturality
    (dplus.inv.app K)
  dsimp only [Functor.comp_map] at hcore
  rw [hd] at hcore
  dsimp [fixedCompactSupportComparisonIso, fixedDirectImageComparisonIso,
    compactSupportSiteComparison, compactSupportSiteComparisonPlus,
    rightDerivedLowerShriekOfCompactificationPlusCompatibility,
    Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility,
    Functor.mapDerivedCategoryPlusCompatibility]
  repeat' erw [CategoryTheory.Functor.map_id]
  simp only [Category.id_comp, Category.comp_id, Category.assoc,
    CategoryTheory.Functor.map_comp]
  let := isIso_fixedComparisonDirectImageMatePlus R c.g
  repeat' erw [Category.id_comp]
  have h := congrArg (fun t ↦ t ≫
    ((inv (fixedComparisonDirectImageMatePlus R c.g)).app
      (L.mapDerivedCategoryPlus.obj K)).hom ≫
    V.mapDerivedCategory.map
      ((Etale.lowerStar C c.g).rightDerivedFunctorPlusCompatibility.hom.app
        (L.mapDerivedCategoryPlus.obj K))) hcore
  dsimp only [d, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app] at h
  dsimp only [T, U, V, L, L', G, C, dplus, Functor.comp_obj] at h
  simpa only [CategoryTheory.Functor.map_comp, Category.assoc, e,
    C, Functor.mapDerivedCategoryPlus, _root_.DerivedCategory.Plus.ι,
    ObjectProperty.lift, ObjectProperty.ι, inducedFunctor,
    Functor.comp_obj, Functor.comp_map] using h

end AlgebraicGeometry.ProEtale

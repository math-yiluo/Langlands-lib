/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.CategoryTheory.NativeRingedRestrictionHom
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

/-! # Derived internal Hom under equivalences of sites

Source: Stacks 03A0, 03CH, 03DA, 03DG, 08J7 and 0A95.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe c d vc vd r w w'
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.NativeRestriction

/-- Restriction by a site equivalence commutes with derived internal Hom.

Source: Stacks 03A0, 03CH, 03DA, 03DG, 08J7 and 0A95.
(auxiliary; not a blueprint node).

Proof: choose a complex representing L and a K-injective complex representing M.
An exact additive equivalence preserves K-injectives. Compute the two derived Hom
objects using these representatives, restrict their Hom complex using the ordinary
restriction comparison, and use the localization factorization of the derived functor.
The site-object, site-arrow, coefficient and derived universes remain independent. -/
theorem derivedHomRestriction
    {C : Type c} {D : Type d} [Category.{vc} C] [Category.{vd} D]
    {K : GrothendieckTopology C} {J : GrothendieckTopology D}
    (F : C ⥤ D) [Functor.IsContinuous F K J]
    (R : Sheaf J CommRingCat.{max c d vc vd r})
    (hF : ∀ X : C, (Over.post (X := X) F).IsEquivalence)
    [(restrictModules.{_, _, _, _, r} (K := K) F R).IsEquivalence]
    [HasSheafify J AddCommGrpCat.{max c d vc vd r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c d vc vd r}]
    [HasSheafify K AddCommGrpCat.{max c d vc vd r}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{max c d vc vd r}]
    [HasDerivedCategory.{w} (NativeModules.{max c d vc vd r, d, vd} R)]
    [HasDerivedCategory.{w'} (NativeModules.{max c d vc vd r, c, vc}
      (restrictedCommRing.{_, _, _, _, r} (K := K) F R))]
    (L M : DerivedCategory (NativeModules.{max c d vc vd r, d, vd} R)) :
    let T := restrictModules.{_, _, _, _, r} (K := K) F R
    let S := restrictedCommRing.{_, _, _, _, r} (K := K) F R
    Nonempty (T.mapDerivedCategory.obj
      ((derivedInternalHomOfUniverses.{d, vd, max c vc r, w} J R).obj (op L, M)) ≅
        (derivedInternalHomOfUniverses.{c, vc, max d vd r, w'} K S).obj
          (op (T.mapDerivedCategory.obj L), T.mapDerivedCategory.obj M)) := by
  let T := restrictModules.{_, _, _, _, r} (K := K) F R
  let S := restrictedCommRing.{_, _, _, _, r} (K := K) F R
  let Tc := T.mapHomologicalComplex (.up ℤ)
  let : IsGrothendieckAbelian.{max c d vc vd r}
      (NativeModules.{max c d vc vd r, d, vd} R) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{d, vd,
      max c vc r}
      J R).1
  let Lc := DerivedCategory.Q.objPreimage L
  let Mc := DerivedCategory.Q.objPreimage M
  obtain ⟨Ic, hIc, j, _, hj⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective Mc
  let := hIc
  let := hj
  let eL : DerivedCategory.Q.obj Lc ≅ L := DerivedCategory.Q.objObjPreimageIso L
  let eM : DerivedCategory.Q.obj Ic ≅ M :=
    (asIso (DerivedCategory.Q.map j)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso M
  obtain ⟨α⟩ := derivedInternalHomOfUniverses_obj_iso.{d, vd, max c vc r, w}
    J R L M Lc Ic eL eM
  let eL' : DerivedCategory.Q.obj (Tc.obj Lc) ≅ T.mapDerivedCategory.obj L :=
    (T.mapDerivedCategoryFactors.app Lc).symm ≪≫ T.mapDerivedCategory.mapIso eL
  let eM' : DerivedCategory.Q.obj (Tc.obj Ic) ≅ T.mapDerivedCategory.obj M :=
    (T.mapDerivedCategoryFactors.app Ic).symm ≪≫ T.mapDerivedCategory.mapIso eM
  obtain ⟨β⟩ := derivedInternalHomOfUniverses_obj_iso.{c, vc, max d vd r, w'} K S
    (T.mapDerivedCategory.obj L) (T.mapDerivedCategory.obj M)
    (Tc.obj Lc) (Tc.obj Ic) eL' eM'
  obtain ⟨γ⟩ := homComplexRestriction.{_, _, _, _, r} (K := K) F R hF Lc Ic
  exact ⟨T.mapDerivedCategory.mapIso α ≪≫
    T.mapDerivedCategoryFactors.app (homComplex (R := R) Lc Ic) ≪≫
      DerivedCategory.Q.mapIso γ ≪≫ β.symm⟩

end CategoryTheory.NativeRestriction

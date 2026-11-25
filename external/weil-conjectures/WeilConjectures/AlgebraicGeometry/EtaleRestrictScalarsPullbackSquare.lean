/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleRestrictScalarsFunctorComparisons
import WeilConjectures.SixFunctors.BaseChange.DerivedComparison
import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Vertical

/-! # Coefficient compatibility of derived pullback squares -/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace CategoryTheory

private noncomputable def homotopy_square {A B B' C : Type*}
    [Category A] [Category B] [Category B'] [Category C]
    [Preadditive A] [Preadditive B] [Preadditive B'] [Preadditive C]
    (F : A ⥤ B) (G : B ⥤ C) (F' : A ⥤ B') (G' : B' ⥤ C)
    [F.Additive] [G.Additive] [F'.Additive] [G'.Additive] (a : F ⋙ G ⟶ F' ⋙ G') :
    F.mapHomotopyCategoryPlus ⋙ G.mapHomotopyCategoryPlus ⟶
      F'.mapHomotopyCategoryPlus ⋙ G'.mapHomotopyCategoryPlus :=
  (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).hom ≫
    NatTrans.mapHomotopyCategoryPlus a ≫
    (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F' ⋙ G'))).inv

private lemma homotopy_square_app {A B B' C : Type*}
    [Category A] [Category B] [Category B'] [Category C]
    [Preadditive A] [Preadditive B] [Preadditive B'] [Preadditive C]
    (F : A ⥤ B) (G : B ⥤ C) (F' : A ⥤ B') (G' : B' ⥤ C)
    [F.Additive] [G.Additive] [F'.Additive] [G'.Additive] (a : F ⋙ G ⟶ F' ⋙ G')
    (K : HomotopyCategory.Plus A) :
    (homotopy_square F G F' G' a).app K =
      (NatTrans.mapHomotopyCategoryPlus a).app K := by
  simp only [homotopy_square, NatTrans.comp_app,
    Functor.mapHomotopyCategoryPlusCompIso_refl_hom_app,
    Functor.mapHomotopyCategoryPlusCompIso_refl_inv_app, Category.id_comp, Category.comp_id]


private lemma map_square_fac {C D D' E : Type*}
    [Category C] [Category D] [Category D'] [Category E]
    [Abelian C] [Abelian D] [Abelian D'] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory D']
    [HasDerivedCategory E]
    (F : C ⥤ D) (G : D ⥤ E) (F' : C ⥤ D') (G' : D' ⥤ E)
    [F.Additive] [G.Additive] [F'.Additive] [G'.Additive]
    [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
    [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]
    [Limits.PreservesFiniteLimits F'] [Limits.PreservesFiniteColimits F']
    [Limits.PreservesFiniteLimits G'] [Limits.PreservesFiniteColimits G']
    (a : F ⋙ G ≅ F' ⋙ G')
    (aD : F.mapDerivedCategoryPlus ⋙ G.mapDerivedCategoryPlus ≅
      F'.mapDerivedCategoryPlus ⋙ G'.mapDerivedCategoryPlus)
    (haD : aD = (Functor.mapDerivedCategoryPlusCompIso F G).symm ≪≫
      Functor.mapDerivedCategoryPlusNatIso a ≪≫ Functor.mapDerivedCategoryPlusCompIso F' G')
    (K : HomotopyCategory.Plus C) :
    aD.hom.app (DerivedCategory.Plus.Qh.obj K) ≫
      G'.mapDerivedCategoryPlus.map (F'.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
      G'.mapDerivedCategoryPlusFactorsh.hom.app (F'.mapHomotopyCategoryPlus.obj K) =
    G.mapDerivedCategoryPlus.map (F.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
      G.mapDerivedCategoryPlusFactorsh.hom.app (F.mapHomotopyCategoryPlus.obj K) ≫
      DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus a.hom).app K) := by
  subst aD
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryPlusCompIso_hom_app_factorsh,
    Functor.mapDerivedCategoryPlusNatIso_hom_app_factorsh,
    ← Functor.mapDerivedCategoryPlusCompIso_hom_app_factorsh F G K]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]


section
private lemma path_fac {A B C A' B' C' : Type*}
  [Category A] [Category B] [Category C] [Category A'] [Category B'] [Category C']
  [Abelian A] [Abelian B] [Abelian C] [Abelian A'] [Abelian B'] [Abelian C']
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  [HasDerivedCategory A'] [HasDerivedCategory B'] [HasDerivedCategory C']
  (R : A' ⥤ A) (S : B' ⥤ B) (T : C' ⥤ C)
  (F : A ⥤ B) (G : B ⥤ C) (F' : A' ⥤ B') (G' : B' ⥤ C')
  [R.Additive] [S.Additive] [T.Additive] [F.Additive] [G.Additive]
  [F'.Additive] [G'.Additive]
  [Limits.PreservesFiniteLimits R] [Limits.PreservesFiniteColimits R]
  [Limits.PreservesFiniteLimits S] [Limits.PreservesFiniteColimits S]
  [Limits.PreservesFiniteLimits T] [Limits.PreservesFiniteColimits T]
  [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
  [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]
  [Limits.PreservesFiniteLimits F'] [Limits.PreservesFiniteColimits F']
  [Limits.PreservesFiniteLimits G'] [Limits.PreservesFiniteColimits G']
  (aD : R.mapDerivedCategoryPlus ⋙ F.mapDerivedCategoryPlus ≅
    F'.mapDerivedCategoryPlus ⋙ S.mapDerivedCategoryPlus)
  (bD : S.mapDerivedCategoryPlus ⋙ G.mapDerivedCategoryPlus ≅
    G'.mapDerivedCategoryPlus ⋙ T.mapDerivedCategoryPlus)
  (aH : R.mapHomotopyCategoryPlus ⋙ F.mapHomotopyCategoryPlus ⟶
    F'.mapHomotopyCategoryPlus ⋙ S.mapHomotopyCategoryPlus)
  (bH : S.mapHomotopyCategoryPlus ⋙ G.mapHomotopyCategoryPlus ⟶
    G'.mapHomotopyCategoryPlus ⋙ T.mapHomotopyCategoryPlus)
  (ha : ∀ K, aD.hom.app (DerivedCategory.Plus.Qh.obj K) ≫
    S.mapDerivedCategoryPlus.map (F'.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
    S.mapDerivedCategoryPlusFactorsh.hom.app (F'.mapHomotopyCategoryPlus.obj K) =
    F.mapDerivedCategoryPlus.map (R.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
    F.mapDerivedCategoryPlusFactorsh.hom.app (R.mapHomotopyCategoryPlus.obj K) ≫
    DerivedCategory.Plus.Qh.map (aH.app K))
  (hb : ∀ K, bD.hom.app (DerivedCategory.Plus.Qh.obj K) ≫
    T.mapDerivedCategoryPlus.map (G'.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
    T.mapDerivedCategoryPlusFactorsh.hom.app (G'.mapHomotopyCategoryPlus.obj K) =
    G.mapDerivedCategoryPlus.map (S.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
    G.mapDerivedCategoryPlusFactorsh.hom.app (S.mapHomotopyCategoryPlus.obj K) ≫
    DerivedCategory.Plus.Qh.map (bH.app K))
    (K : HomotopyCategory.Plus A') :
    G.mapDerivedCategoryPlus.map (aD.hom.app (DerivedCategory.Plus.Qh.obj K)) ≫
      bD.hom.app (F'.mapDerivedCategoryPlus.obj (DerivedCategory.Plus.Qh.obj K)) ≫
      T.mapDerivedCategoryPlus.map
        (G'.mapDerivedCategoryPlus.map (F'.mapDerivedCategoryPlusFactorsh.hom.app K)) ≫
      T.mapDerivedCategoryPlus.map
        (G'.mapDerivedCategoryPlusFactorsh.hom.app (F'.mapHomotopyCategoryPlus.obj K)) ≫
      T.mapDerivedCategoryPlusFactorsh.hom.app
        (G'.mapHomotopyCategoryPlus.obj (F'.mapHomotopyCategoryPlus.obj K)) =
    G.mapDerivedCategoryPlus.map
        (F.mapDerivedCategoryPlus.map (R.mapDerivedCategoryPlusFactorsh.hom.app K)) ≫
      G.mapDerivedCategoryPlus.map (F.mapDerivedCategoryPlusFactorsh.hom.app
        (R.mapHomotopyCategoryPlus.obj K)) ≫
      G.mapDerivedCategoryPlusFactorsh.hom.app
        (F.mapHomotopyCategoryPlus.obj (R.mapHomotopyCategoryPlus.obj K)) ≫
      DerivedCategory.Plus.Qh.map
        (G.mapHomotopyCategoryPlus.map (aH.app K) ≫
          bH.app (F'.mapHomotopyCategoryPlus.obj K)) := by
  have hn := bD.hom.naturality (F'.mapDerivedCategoryPlusFactorsh.hom.app K)
  have hnat := G.mapDerivedCategoryPlusFactorsh.hom.naturality (aH.app K)
  simp only [Functor.comp_map, Functor.comp_obj] at hn hnat
  rw [← reassoc_of% hn, hb]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc,
    Category.assoc (aD.hom.app _), ha]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hnat]
end
section Cube
private lemma derived_cube {A B C D A' B' C' D' : Type*}
  [Category A] [Category B] [Category C]
  [Category D] [Category A'] [Category B']
  [Category C'] [Category D']
  [Abelian A] [Abelian B] [Abelian C]
  [Abelian D] [Abelian A'] [Abelian B']
  [Abelian C'] [Abelian D']
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  [HasDerivedCategory D] [HasDerivedCategory A'] [HasDerivedCategory B']
  [HasDerivedCategory C'] [HasDerivedCategory D']
  (R : A' ⥤ A)
  (S : B' ⥤ B)
  (T : C' ⥤ C)
  (U : D' ⥤ D)
  (F : A ⥤ B)
  (G : B ⥤ C)
  (H : A ⥤ D)
  (I : D ⥤ C)
  (F' : A' ⥤ B')
  (G' : B' ⥤ C')
  (H' : A' ⥤ D')
  (I' : D' ⥤ C')
  [R.Additive] [Limits.PreservesFiniteLimits R] [Limits.PreservesFiniteColimits R]
  [S.Additive] [Limits.PreservesFiniteLimits S] [Limits.PreservesFiniteColimits S]
  [T.Additive] [Limits.PreservesFiniteLimits T] [Limits.PreservesFiniteColimits T]
  [U.Additive] [Limits.PreservesFiniteLimits U] [Limits.PreservesFiniteColimits U]
  [F.Additive] [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
  [G.Additive] [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]
  [H.Additive] [Limits.PreservesFiniteLimits H] [Limits.PreservesFiniteColimits H]
  [I.Additive] [Limits.PreservesFiniteLimits I] [Limits.PreservesFiniteColimits I]
  [F'.Additive] [Limits.PreservesFiniteLimits F'] [Limits.PreservesFiniteColimits F']
  [G'.Additive] [Limits.PreservesFiniteLimits G'] [Limits.PreservesFiniteColimits G']
  [H'.Additive] [Limits.PreservesFiniteLimits H'] [Limits.PreservesFiniteColimits H']
  [I'.Additive] [Limits.PreservesFiniteLimits I'] [Limits.PreservesFiniteColimits I']
  (aD : R.mapDerivedCategoryPlus ⋙ F.mapDerivedCategoryPlus ≅
    F'.mapDerivedCategoryPlus ⋙ S.mapDerivedCategoryPlus)
  (aH : R.mapHomotopyCategoryPlus ⋙ F.mapHomotopyCategoryPlus ⟶
    F'.mapHomotopyCategoryPlus ⋙ S.mapHomotopyCategoryPlus)
  (ha : ∀ K, aD.hom.app (DerivedCategory.Plus.Qh.obj K) ≫
    S.mapDerivedCategoryPlus.map (F'.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
    S.mapDerivedCategoryPlusFactorsh.hom.app (F'.mapHomotopyCategoryPlus.obj K) =
    F.mapDerivedCategoryPlus.map (R.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
    F.mapDerivedCategoryPlusFactorsh.hom.app (R.mapHomotopyCategoryPlus.obj K) ≫
    DerivedCategory.Plus.Qh.map (aH.app K))
  (bD : S.mapDerivedCategoryPlus ⋙ G.mapDerivedCategoryPlus ≅
    G'.mapDerivedCategoryPlus ⋙ T.mapDerivedCategoryPlus)
  (bH : S.mapHomotopyCategoryPlus ⋙ G.mapHomotopyCategoryPlus ⟶
    G'.mapHomotopyCategoryPlus ⋙ T.mapHomotopyCategoryPlus)
  (hb : ∀ K, bD.hom.app (DerivedCategory.Plus.Qh.obj K) ≫
    T.mapDerivedCategoryPlus.map (G'.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
    T.mapDerivedCategoryPlusFactorsh.hom.app (G'.mapHomotopyCategoryPlus.obj K) =
    G.mapDerivedCategoryPlus.map (S.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
    G.mapDerivedCategoryPlusFactorsh.hom.app (S.mapHomotopyCategoryPlus.obj K) ≫
    DerivedCategory.Plus.Qh.map (bH.app K))
  (cD : R.mapDerivedCategoryPlus ⋙ H.mapDerivedCategoryPlus ≅
    H'.mapDerivedCategoryPlus ⋙ U.mapDerivedCategoryPlus)
  (cH : R.mapHomotopyCategoryPlus ⋙ H.mapHomotopyCategoryPlus ⟶
    H'.mapHomotopyCategoryPlus ⋙ U.mapHomotopyCategoryPlus)
  (hc : ∀ K, cD.hom.app (DerivedCategory.Plus.Qh.obj K) ≫
    U.mapDerivedCategoryPlus.map (H'.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
    U.mapDerivedCategoryPlusFactorsh.hom.app (H'.mapHomotopyCategoryPlus.obj K) =
    H.mapDerivedCategoryPlus.map (R.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
    H.mapDerivedCategoryPlusFactorsh.hom.app (R.mapHomotopyCategoryPlus.obj K) ≫
    DerivedCategory.Plus.Qh.map (cH.app K))
  (dD : U.mapDerivedCategoryPlus ⋙ I.mapDerivedCategoryPlus ≅
    I'.mapDerivedCategoryPlus ⋙ T.mapDerivedCategoryPlus)
  (dH : U.mapHomotopyCategoryPlus ⋙ I.mapHomotopyCategoryPlus ⟶
    I'.mapHomotopyCategoryPlus ⋙ T.mapHomotopyCategoryPlus)
  (hd : ∀ K, dD.hom.app (DerivedCategory.Plus.Qh.obj K) ≫
    T.mapDerivedCategoryPlus.map (I'.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
    T.mapDerivedCategoryPlusFactorsh.hom.app (I'.mapHomotopyCategoryPlus.obj K) =
    I.mapDerivedCategoryPlus.map (U.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
    I.mapDerivedCategoryPlusFactorsh.hom.app (U.mapHomotopyCategoryPlus.obj K) ≫
    DerivedCategory.Plus.Qh.map (dH.app K))
  (tD : F.mapDerivedCategoryPlus ⋙ G.mapDerivedCategoryPlus ≅
    H.mapDerivedCategoryPlus ⋙ I.mapDerivedCategoryPlus)
  (tH : F.mapHomotopyCategoryPlus ⋙ G.mapHomotopyCategoryPlus ⟶
    H.mapHomotopyCategoryPlus ⋙ I.mapHomotopyCategoryPlus)
  (ht : ∀ K, tD.hom.app (DerivedCategory.Plus.Qh.obj K) ≫
    I.mapDerivedCategoryPlus.map (H.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
    I.mapDerivedCategoryPlusFactorsh.hom.app (H.mapHomotopyCategoryPlus.obj K) =
    G.mapDerivedCategoryPlus.map (F.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
    G.mapDerivedCategoryPlusFactorsh.hom.app (F.mapHomotopyCategoryPlus.obj K) ≫
    DerivedCategory.Plus.Qh.map (tH.app K))
  (t'D : F'.mapDerivedCategoryPlus ⋙ G'.mapDerivedCategoryPlus ≅
    H'.mapDerivedCategoryPlus ⋙ I'.mapDerivedCategoryPlus)
  (t'H : F'.mapHomotopyCategoryPlus ⋙ G'.mapHomotopyCategoryPlus ⟶
    H'.mapHomotopyCategoryPlus ⋙ I'.mapHomotopyCategoryPlus)
  (ht' : ∀ K, t'D.hom.app (DerivedCategory.Plus.Qh.obj K) ≫
    I'.mapDerivedCategoryPlus.map (H'.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
    I'.mapDerivedCategoryPlusFactorsh.hom.app (H'.mapHomotopyCategoryPlus.obj K) =
    G'.mapDerivedCategoryPlus.map (F'.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
    G'.mapDerivedCategoryPlusFactorsh.hom.app (F'.mapHomotopyCategoryPlus.obj K) ≫
    DerivedCategory.Plus.Qh.map (t'H.app K))
  (hcube : ∀ K, G.mapHomotopyCategoryPlus.map (aH.app K) ≫
    bH.app (F'.mapHomotopyCategoryPlus.obj K) ≫ T.mapHomotopyCategoryPlus.map (t'H.app K) =
    tH.app (R.mapHomotopyCategoryPlus.obj K) ≫ I.mapHomotopyCategoryPlus.map (cH.app K) ≫
      dH.app (H'.mapHomotopyCategoryPlus.obj K)) :
    Functor.whiskerRight aD.hom G.mapDerivedCategoryPlus ≫
      Functor.whiskerLeft F'.mapDerivedCategoryPlus bD.hom ≫
      Functor.whiskerRight t'D.hom T.mapDerivedCategoryPlus =
    Functor.whiskerLeft R.mapDerivedCategoryPlus tD.hom ≫
      Functor.whiskerRight cD.hom I.mapDerivedCategoryPlus ≫
      Functor.whiskerLeft H'.mapDerivedCategoryPlus dD.hom := by
  refine Localization.natTrans_ext DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso _) (fun K ↦ ?_)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  rw [← cancel_mono (T.mapDerivedCategoryPlus.map
      (I'.mapDerivedCategoryPlus.map (H'.mapDerivedCategoryPlusFactorsh.hom.app K)) ≫
    T.mapDerivedCategoryPlus.map
      (I'.mapDerivedCategoryPlusFactorsh.hom.app (H'.mapHomotopyCategoryPlus.obj K)) ≫
    T.mapDerivedCategoryPlusFactorsh.hom.app
      (I'.mapHomotopyCategoryPlus.obj (H'.mapHomotopyCategoryPlus.obj K)))]
  have hnat := T.mapDerivedCategoryPlusFactorsh.hom.naturality (t'H.app K)
  have hnat' := tD.hom.naturality (R.mapDerivedCategoryPlusFactorsh.hom.app K)
  simp only [Functor.comp_obj, Functor.comp_map] at hnat hnat'
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc,
    Category.assoc (t'D.hom.app _), ht' K]
  simp only [Functor.map_comp, Category.assoc]
  rw [hnat]
  slice_lhs 1 5 =>
    rw [path_fac R S T F G F' G' aD bD aH bH ha hb K]
  slice_rhs 2 6 =>
    rw [path_fac R U T H I H' I' cD dD cH dH hc hd K]
  simp only [Category.assoc]
  rw [← reassoc_of% hnat']
  slice_rhs 2 4 => rw [ht]
  simp only [Category.assoc]
  simp only [← DerivedCategory.Plus.Qh.map_comp]
  rw [Category.assoc, hcube K]

end Cube
private lemma homotopy_cube {A B C D A' B' C' D' : Type*}
    [Category A] [Category B] [Category C]
    [Category D] [Category A'] [Category B']
    [Category C'] [Category D']
    [Preadditive A] [Preadditive B] [Preadditive C]
    [Preadditive D] [Preadditive A'] [Preadditive B']
    [Preadditive C'] [Preadditive D']
    (R : A' ⥤ A) [R.Additive]
    (S : B' ⥤ B) [S.Additive]
    (T : C' ⥤ C) [T.Additive]
    (U : D' ⥤ D) [U.Additive]
    (F : A ⥤ B) [F.Additive]
    (G : B ⥤ C) [G.Additive]
    (H : A ⥤ D) [H.Additive]
    (I : D ⥤ C) [I.Additive]
    (F' : A' ⥤ B') [F'.Additive]
    (G' : B' ⥤ C') [G'.Additive]
    (H' : A' ⥤ D') [H'.Additive]
    (I' : D' ⥤ C') [I'.Additive]
    (a : R ⋙ F ⟶ F' ⋙ S)
    (b : S ⋙ G ⟶ G' ⋙ T)
    (c : R ⋙ H ⟶ H' ⋙ U)
    (d : U ⋙ I ⟶ I' ⋙ T)
    (t : F ⋙ G ⟶ H ⋙ I)
    (t' : F' ⋙ G' ⟶ H' ⋙ I')
    (hcube : ∀ L, G.map (a.app L) ≫ b.app (F'.obj L) ≫ T.map (t'.app L) =
      t.app (R.obj L) ≫ I.map (c.app L) ≫ d.app (H'.obj L))
    (K : HomotopyCategory.Plus A') :
    G.mapHomotopyCategoryPlus.map ((NatTrans.mapHomotopyCategoryPlus a).app K) ≫
      (NatTrans.mapHomotopyCategoryPlus b).app (F'.mapHomotopyCategoryPlus.obj K) ≫
      T.mapHomotopyCategoryPlus.map ((NatTrans.mapHomotopyCategoryPlus t').app K) =
    (NatTrans.mapHomotopyCategoryPlus t).app (R.mapHomotopyCategoryPlus.obj K) ≫
      I.mapHomotopyCategoryPlus.map ((NatTrans.mapHomotopyCategoryPlus c).app K) ≫
      (NatTrans.mapHomotopyCategoryPlus d).app (H'.mapHomotopyCategoryPlus.obj K) := by
  have hs :
      Functor.whiskerRight a G ≫ Functor.whiskerLeft F' b ≫ Functor.whiskerRight t' T =
      Functor.whiskerLeft R t ≫ Functor.whiskerRight c I ≫ Functor.whiskerLeft H' d := by
    apply NatTrans.ext
    funext L
    exact hcube L
  have key := congrArg (fun τ ↦ (NatTrans.mapHomotopyCategoryPlus τ).app K) hs
  simpa only [NatTrans.mapHomotopyCategoryPlus_comp, NatTrans.comp_app,
    NatTrans.mapHomotopyCategoryPlus_whiskerLeft_app,
    NatTrans.mapHomotopyCategoryPlus_whiskerRight_app] using key


private lemma derived_base_cube {A B C D A' B' C' D' : Type*}
  [Category A] [Category B] [Category C]
  [Category D] [Category A'] [Category B']
  [Category C'] [Category D']
  [Abelian A] [Abelian B] [Abelian C]
  [Abelian D] [Abelian A'] [Abelian B']
  [Abelian C'] [Abelian D']
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  [HasDerivedCategory D] [HasDerivedCategory A'] [HasDerivedCategory B']
  [HasDerivedCategory C'] [HasDerivedCategory D']
  (R : A' ⥤ A)
  (S : B' ⥤ B)
  (T : C' ⥤ C)
  (U : D' ⥤ D)
  (F : A ⥤ B)
  (G : B ⥤ C)
  (H : A ⥤ D)
  (I : D ⥤ C)
  (F' : A' ⥤ B')
  (G' : B' ⥤ C')
  (H' : A' ⥤ D')
  (I' : D' ⥤ C')
  [R.Additive] [Limits.PreservesFiniteLimits R] [Limits.PreservesFiniteColimits R]
  [S.Additive] [Limits.PreservesFiniteLimits S] [Limits.PreservesFiniteColimits S]
  [T.Additive] [Limits.PreservesFiniteLimits T] [Limits.PreservesFiniteColimits T]
  [U.Additive] [Limits.PreservesFiniteLimits U] [Limits.PreservesFiniteColimits U]
  [F.Additive] [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
  [G.Additive] [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]
  [H.Additive] [Limits.PreservesFiniteLimits H] [Limits.PreservesFiniteColimits H]
  [I.Additive] [Limits.PreservesFiniteLimits I] [Limits.PreservesFiniteColimits I]
  [F'.Additive] [Limits.PreservesFiniteLimits F'] [Limits.PreservesFiniteColimits F']
  [G'.Additive] [Limits.PreservesFiniteLimits G'] [Limits.PreservesFiniteColimits G']
  [H'.Additive] [Limits.PreservesFiniteLimits H'] [Limits.PreservesFiniteColimits H']
  [I'.Additive] [Limits.PreservesFiniteLimits I'] [Limits.PreservesFiniteColimits I']
  (a : R ⋙ F ≅ F' ⋙ S)
  (b : S ⋙ G ≅ G' ⋙ T)
  (c : R ⋙ H ≅ H' ⋙ U)
  (d : U ⋙ I ≅ I' ⋙ T)
  (t : F ⋙ G ⟶ H ⋙ I)
  (t' : F' ⋙ G' ⟶ H' ⋙ I')
  (aD : R.mapDerivedCategoryPlus ⋙ F.mapDerivedCategoryPlus ≅
    F'.mapDerivedCategoryPlus ⋙ S.mapDerivedCategoryPlus)
  (bD : S.mapDerivedCategoryPlus ⋙ G.mapDerivedCategoryPlus ≅
    G'.mapDerivedCategoryPlus ⋙ T.mapDerivedCategoryPlus)
  (cD : R.mapDerivedCategoryPlus ⋙ H.mapDerivedCategoryPlus ≅
    H'.mapDerivedCategoryPlus ⋙ U.mapDerivedCategoryPlus)
  (dD : U.mapDerivedCategoryPlus ⋙ I.mapDerivedCategoryPlus ≅
    I'.mapDerivedCategoryPlus ⋙ T.mapDerivedCategoryPlus)
  (tD : F.mapDerivedCategoryPlus ⋙ G.mapDerivedCategoryPlus ≅
    H.mapDerivedCategoryPlus ⋙ I.mapDerivedCategoryPlus)
  (t'D : F'.mapDerivedCategoryPlus ⋙ G'.mapDerivedCategoryPlus ≅
    H'.mapDerivedCategoryPlus ⋙ I'.mapDerivedCategoryPlus)
  (haD : aD = (Functor.mapDerivedCategoryPlusCompIso R F).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso a ≪≫ Functor.mapDerivedCategoryPlusCompIso F' S)
  (hbD : bD = (Functor.mapDerivedCategoryPlusCompIso S G).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso b ≪≫ Functor.mapDerivedCategoryPlusCompIso G' T)
  (hcD : cD = (Functor.mapDerivedCategoryPlusCompIso R H).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso c ≪≫ Functor.mapDerivedCategoryPlusCompIso H' U)
  (hdD : dD = (Functor.mapDerivedCategoryPlusCompIso U I).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso d ≪≫ Functor.mapDerivedCategoryPlusCompIso I' T)
  (ht : ∀ K, tD.hom.app (DerivedCategory.Plus.Qh.obj K) ≫
    I.mapDerivedCategoryPlus.map (H.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
    I.mapDerivedCategoryPlusFactorsh.hom.app (H.mapHomotopyCategoryPlus.obj K) =
    G.mapDerivedCategoryPlus.map (F.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
    G.mapDerivedCategoryPlusFactorsh.hom.app (F.mapHomotopyCategoryPlus.obj K) ≫
    DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus t).app K))
  (ht' : ∀ K, t'D.hom.app (DerivedCategory.Plus.Qh.obj K) ≫
    I'.mapDerivedCategoryPlus.map (H'.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
    I'.mapDerivedCategoryPlusFactorsh.hom.app (H'.mapHomotopyCategoryPlus.obj K) =
    G'.mapDerivedCategoryPlus.map (F'.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
    G'.mapDerivedCategoryPlusFactorsh.hom.app (F'.mapHomotopyCategoryPlus.obj K) ≫
    DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus t').app K))
  (hcube : ∀ L, G.map (a.hom.app L) ≫ b.hom.app (F'.obj L) ≫ T.map (t'.app L) =
    t.app (R.obj L) ≫ I.map (c.hom.app L) ≫ d.hom.app (H'.obj L)) :
    Functor.whiskerRight aD.hom G.mapDerivedCategoryPlus ≫
      Functor.whiskerLeft F'.mapDerivedCategoryPlus bD.hom ≫
      Functor.whiskerRight t'D.hom T.mapDerivedCategoryPlus =
    Functor.whiskerLeft R.mapDerivedCategoryPlus tD.hom ≫
      Functor.whiskerRight cD.hom I.mapDerivedCategoryPlus ≫
      Functor.whiskerLeft H'.mapDerivedCategoryPlus dD.hom := by
  apply derived_cube R S T U F G H I F' G' H' I'
    (aD := aD) (bD := bD) (cD := cD) (dD := dD) (tD := tD) (t'D := t'D)
    (aH := homotopy_square R F F' S a.hom)
    (bH := homotopy_square S G G' T b.hom)
    (cH := homotopy_square R H H' U c.hom)
    (dH := homotopy_square U I I' T d.hom)
    (tH := homotopy_square F G H I t)
    (t'H := homotopy_square F' G' H' I' t')
  · intro K
    rw [homotopy_square_app]
    exact map_square_fac R F F' S a aD haD K
  · intro K
    rw [homotopy_square_app]
    exact map_square_fac S G G' T b bD hbD K
  · intro K
    rw [homotopy_square_app]
    exact map_square_fac R H H' U c cD hcD K
  · intro K
    rw [homotopy_square_app]
    exact map_square_fac U I I' T d dD hdD K
  · intro K
    rw [homotopy_square_app]
    exact ht K
  · intro K
    rw [homotopy_square_app]
    exact ht' K
  · intro K
    simp only [homotopy_square_app]
    exact homotopy_cube R S T U F G H I F' G' H' I'
      a.hom b.hom c.hom d.hom t t' hcube K

end CategoryTheory

private lemma conjugate_unique {C D : Type*} [Category* C] [Category* D]
    {F F' : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) (b : F' ⊣ G) :
    conjugateEquiv b a (a.leftAdjointUniq b).hom = 𝟙 G := by
  simp [Adjunction.leftAdjointUniq]

private lemma conjugate_assoc_inv {A B C D : Type*}
    [Category* A] [Category* B] [Category* C] [Category* D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : B ⥤ C} {R₂ : C ⥤ B}
    {L₃ : C ⥤ D} {R₃ : D ⥤ C}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (c : L₃ ⊣ R₃) :
    conjugateEquiv ((a.comp b).comp c) (a.comp (b.comp c))
      (Functor.associator L₁ L₂ L₃).inv = (Functor.associator R₃ R₂ R₁).inv := by
  apply (cancel_epi (Functor.associator R₃ R₂ R₁).hom).mp
  rw [← conjugateEquiv_associator_hom a b c, conjugateEquiv_comp]
  simp only [Iso.inv_hom_id]
  rw [conjugateEquiv_associator_hom]
  simp

namespace AlgebraicGeometry.Etale

private lemma coefficient_comp
    {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ')
    {X S Y : Scheme.{u}} (h : Y ⟶ X) (p : X ⟶ S) (d : Y ⟶ S)
    (hd : d = h ≫ p) :
    Functor.isoWhiskerLeft (Sheaf.restrictScalars S.smallEtaleTopology φ)
        (upperStarComp (ModuleCat.{u + 1} Λ) h p d hd) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (upperStarRestrictScalarsIsoSheaf φ p) (h)^*[ModuleCat.{u + 1} Λ] ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (p)^*[ModuleCat.{u + 1} Λ'] (upperStarRestrictScalarsIsoSheaf φ h) ≪≫
      (Functor.associator _ _ _).symm =
    upperStarRestrictScalarsIsoSheaf φ d ≪≫
      Functor.isoWhiskerRight (upperStarComp (ModuleCat.{u + 1} Λ') h p d hd)
        (Sheaf.restrictScalars Y.smallEtaleTopology φ) := by
  have := (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ).isRightAdjoint
  let aS := Sheaf.restrictCoextendScalarsAdj S.smallEtaleTopology φ
  let aX := Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology φ
  let aY := Sheaf.restrictCoextendScalarsAdj Y.smallEtaleTopology φ
  let b := upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p
  let c := upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h
  let f := upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) d
  let b' := upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') p
  let c' := upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') h
  let f' := upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') d
  apply Iso.ext
  apply (conjugateEquiv ((b'.comp c').comp aY) (aS.comp f)).injective
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom]
  rw [← conjugateEquiv_comp _ (aS.comp (b.comp c)),
    ← conjugateEquiv_comp _ ((aS.comp b).comp c),
    ← conjugateEquiv_comp _ ((b'.comp aX).comp c),
    ← conjugateEquiv_comp _ (b'.comp (aX.comp c)),
    ← conjugateEquiv_comp _ (b'.comp (c'.comp aY)),
    ← conjugateEquiv_comp _ (f'.comp aY)]
  rw [conjugate_assoc_inv, conjugateEquiv_whiskerLeft, conjugateEquiv_associator_hom,
    conjugateEquiv_whiskerRight, conjugate_assoc_inv, conjugateEquiv_whiskerLeft,
    conjugateEquiv_whiskerRight]
  have hp := conjugate_unique (aS.comp b) (b'.comp aX)
  have hh := conjugate_unique (aX.comp c) (c'.comp aY)
  have hd' := conjugate_unique (aS.comp f) (f'.comp aY)
  simp only [aS, aX, aY, b, c, f, b', c', f', upperStarRestrictScalarsIsoSheaf] at hp hh hd' ⊢
  erw [hp, hh, hd']
  simp only [upperStarComp, Iso.symm_hom, conjugateIsoEquiv_symm_apply_inv,
    Iso.symm_inv, Equiv.apply_symm_apply]
  apply NatTrans.ext
  funext F
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Functor.associator_hom_app, NatTrans.id_app]
  erw [CategoryTheory.Functor.map_id]
  rfl

private lemma coefficient_comp_app
    {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ')
    {X S Y : Scheme.{u}} (h : Y ⟶ X) (p : X ⟶ S) (d : Y ⟶ S)
    (hd : d = h ≫ p) (L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ')) :
    (upperStarComp (ModuleCat.{u + 1} Λ) h p d hd).hom.app
        ((Sheaf.restrictScalars S.smallEtaleTopology φ).obj L) ≫
      (h)^*[ModuleCat.{u + 1} Λ].map ((upperStarRestrictScalarsIsoSheaf φ p).hom.app L) ≫
      (upperStarRestrictScalarsIsoSheaf φ h).hom.app ((p)^*[ModuleCat.{u + 1} Λ'].obj L) =
    (upperStarRestrictScalarsIsoSheaf φ d).hom.app L ≫
      (Sheaf.restrictScalars Y.smallEtaleTopology φ).map
        ((upperStarComp (ModuleCat.{u + 1} Λ') h p d hd).hom.app L) := by
  have key := congr_app (congrArg Iso.hom (coefficient_comp φ h p d hd)) L
  simpa using key

private lemma coefficient_square
    {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ')
    {X S T Y : Scheme.{u}} {p : X ⟶ S} {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X}
    (sq : CommSq e h g p) (L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ')) :
    (h)^*[ModuleCat.{u + 1} Λ].map ((upperStarRestrictScalarsIsoSheaf φ p).hom.app L) ≫
      (upperStarRestrictScalarsIsoSheaf φ h).hom.app ((p)^*[ModuleCat.{u + 1} Λ'].obj L) ≫
      (Sheaf.restrictScalars Y.smallEtaleTopology φ).map
        ((squareUpperStarIso (ModuleCat.{u + 1} Λ') sq).hom.app L) =
    (squareUpperStarIso (ModuleCat.{u + 1} Λ) sq).hom.app
        ((Sheaf.restrictScalars S.smallEtaleTopology φ).obj L) ≫
      (e)^*[ModuleCat.{u + 1} Λ].map ((upperStarRestrictScalarsIsoSheaf φ g).hom.app L) ≫
      (upperStarRestrictScalarsIsoSheaf φ e).hom.app ((g)^*[ModuleCat.{u + 1} Λ'].obj L) := by
  rw [← cancel_epi ((upperStarComp (ModuleCat.{u + 1} Λ) h p (e ≫ g) sq.w).hom.app
    ((Sheaf.restrictScalars S.smallEtaleTopology φ).obj L))]
  simp only [squareUpperStarIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    CategoryTheory.Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [reassoc_of% (coefficient_comp_app φ h p (e ≫ g) sq.w L),
    ← CategoryTheory.Functor.map_comp_assoc, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  exact (coefficient_comp_app φ e g (e ≫ g) rfl L).symm

/-- Coefficient restriction commutes with the comparison of the two composite
inverse images attached to a commutative square.

Source: Stacks Project, Remark 21.19.3, Tag 07A7, and the composition of inverse images
in the definition of the exchange map.
Proof: for composable morphisms, compare both coefficient transports of their
composite inverse image. Inverse images are left adjoints to the sectionwise direct
images; the coefficient comparison is obtained from the common direct-image/coextension
composite by uniqueness of left adjoints. Uniqueness is transitive and compatible with
composition of adjunctions. Thus the coefficient comparison for a composite equals
the composite of the two coefficient comparisons, with the inverse-image composition
isomorphisms inserted. Apply this once to h followed by p and once to e followed by g.
The equality h ≫ p = e ≫ g identifies the composite comparisons. Composing the first
identity with the inverse of the second gives the asserted square. Apply exact
derivation: Functor.mapDerivedCategoryPlusNatIso preserves composition and its composition
isomorphisms are natural, so the same identity holds in D⁺. No direct-image derived
functor or adjunction unit/counit occurs in this assertion.
(blueprint: lem-sbc-restrict-scalars-pullback-square-comparison) -/
theorem pullbackSquareComparison_restrictScalars
    {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ')
    {X S T Y : Scheme.{u}} {p : X ⟶ S} {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X}
    (sq : CommSq e h g p)
    (L : DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ'))) :
    (D+((h)^*[ModuleCat.{u + 1} Λ])).map
        ((derivedUpperStarRestrictScalarsIso φ p).hom.app L) ≫
      (derivedUpperStarRestrictScalarsIso φ h).hom.app
        ((D+((p)^*[ModuleCat.{u + 1} Λ'])).obj L) ≫
      (Sheaf.restrictScalars Y.smallEtaleTopology φ).mapDerivedCategoryPlus.map
        ((pullbackSquareComparison (ModuleCat.{u + 1} Λ') sq).hom.app L) =
    (pullbackSquareComparison (ModuleCat.{u + 1} Λ) sq).hom.app
        ((Sheaf.restrictScalars S.smallEtaleTopology φ).mapDerivedCategoryPlus.obj L) ≫
      (D+((e)^*[ModuleCat.{u + 1} Λ])).map
        ((derivedUpperStarRestrictScalarsIso φ g).hom.app L) ≫
      (derivedUpperStarRestrictScalarsIso φ e).hom.app
        ((D+((g)^*[ModuleCat.{u + 1} Λ'])).obj L) := by
  have key := CategoryTheory.derived_base_cube
    (R := Sheaf.restrictScalars S.smallEtaleTopology φ)
    (S := Sheaf.restrictScalars X.smallEtaleTopology φ)
    (T := Sheaf.restrictScalars Y.smallEtaleTopology φ)
    (U := Sheaf.restrictScalars T.smallEtaleTopology φ)
    (F := (p)^*[ModuleCat.{u + 1} Λ])
    (G := (h)^*[ModuleCat.{u + 1} Λ])
    (H := (g)^*[ModuleCat.{u + 1} Λ])
    (I := (e)^*[ModuleCat.{u + 1} Λ])
    (F' := (p)^*[ModuleCat.{u + 1} Λ'])
    (G' := (h)^*[ModuleCat.{u + 1} Λ'])
    (H' := (g)^*[ModuleCat.{u + 1} Λ'])
    (I' := (e)^*[ModuleCat.{u + 1} Λ'])
    (a := upperStarRestrictScalarsIsoSheaf φ p)
    (aD := derivedUpperStarRestrictScalarsIso φ p)
    (haD := rfl)
    (b := upperStarRestrictScalarsIsoSheaf φ h)
    (bD := derivedUpperStarRestrictScalarsIso φ h)
    (hbD := rfl)
    (c := upperStarRestrictScalarsIsoSheaf φ g)
    (cD := derivedUpperStarRestrictScalarsIso φ g)
    (hcD := rfl)
    (d := upperStarRestrictScalarsIsoSheaf φ e)
    (dD := derivedUpperStarRestrictScalarsIso φ e)
    (hdD := rfl)
    (t := (squareUpperStarIso (ModuleCat.{u + 1} Λ) sq).hom)
    (tD := pullbackSquareComparison (ModuleCat.{u + 1} Λ) sq)
    (ht := pullbackSquareComparison_hom_app_factorsh (ModuleCat.{u + 1} Λ) sq)
    (t' := (squareUpperStarIso (ModuleCat.{u + 1} Λ') sq).hom)
    (t'D := pullbackSquareComparison (ModuleCat.{u + 1} Λ') sq)
    (ht' := pullbackSquareComparison_hom_app_factorsh (ModuleCat.{u + 1} Λ') sq)
    (hcube := coefficient_square φ sq)
  exact congr_app key L

end AlgebraicGeometry.Etale

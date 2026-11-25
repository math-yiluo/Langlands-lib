/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedExactCompositionComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import Mathlib.Tactic.Convert
import all Mathlib.Algebra.Homology.Localization

/-! # Full-unit normalization of an exact restriction square -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.privateModule false
set_option backward.defeqAttrib.useBackward false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory
section ProofHelpers

universe u_1 u_2 u_3 u_4 v_1 v_2 v_3 v_4

section
variable {C : Type u_1} {D : Type u_2} {C' : Type u_3} {D' : Type u_4}
  [Category.{v_1} C] [Category.{v_2} D] [Category.{v_3} C'] [Category.{v_4} D']
  [Abelian C] [Abelian D] [Abelian C'] [Abelian D']
  [HasDerivedCategory C] [HasDerivedCategory D]
  [HasDerivedCategory C'] [HasDerivedCategory D']
  [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
  [Abelian.HasKInjectiveResolutions C']

private lemma comp_unit_app (F : C ⥤ D) (G : D ⥤ D') [F.Additive] [G.Additive]
    (K : HomotopyCategory C (.up ℤ)) :
    (Functor.rightDerivedFunctorCompUnit F G).app K =
      G.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj K) ≫
        G.rightDerivedFunctor.map (F.rightDerivedFunctorUnit.app K) := by
  have hi : (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app K =
      𝟙 _ := by
    have h := Iso.inv_hom_id_app
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)) K
    erw [Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.comp_id] at h
    exact h
  simp only [Functor.rightDerivedFunctorCompUnit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, hi]
  erw [DerivedCategory.Qh.map_id]
  dsimp
  simp only [Category.id_comp, Category.comp_id]

omit [Abelian.HasKInjectiveResolutions D] in
private lemma comp_map_fac (F : C ⥤ D) (S : D ⥤ D') [F.Additive] [S.Additive]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (K : HomotopyCategory C (.up ℤ)) :
    (F ⋙ S).rightDerivedFunctorUnit.app K ≫
        (Functor.rightDerivedFunctorCompMapDerivedCategoryIso F S).hom.app
          (DerivedCategory.Qh.obj K) =
      S.mapDerivedCategoryFactorsh.inv.app ((F.mapHomotopyCategory (.up ℤ)).obj K) ≫
        S.mapDerivedCategory.map (F.rightDerivedFunctorUnit.app K) := by
  rw [Functor.rightDerivedFunctorCompMapDerivedCategoryIso_hom_fac,
    Functor.rightDerivedFunctorCompMapDerivedCategoryUnit_app']

-- The right-derived restriction square used by derivedComapLowerStarIso.
private noncomputable def derived_square (F : C ⥤ D) (G : C' ⥤ D')
    (R : C ⥤ C') (S : D ⥤ D') [F.Additive] [G.Additive] [R.Additive] [S.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [R.PreservesKInjectiveComplexes] (e : F ⋙ S ≅ R ⋙ G) :
    F.rightDerivedFunctor ⋙ S.mapDerivedCategory ≅ R.mapDerivedCategory ⋙ G.rightDerivedFunctor :=
  (Functor.rightDerivedFunctorCompMapDerivedCategoryIso F S).symm ≪≫
    Functor.rightDerivedFunctorNatIso e ≪≫ Functor.rightDerivedFunctorCompIso R G ≪≫
      Functor.isoWhiskerRight R.rightDerivedFunctorIsoMapDerivedCategory G.rightDerivedFunctor

omit [Abelian.HasKInjectiveResolutions D] in
-- Normalize the square by its right-derived unit before composing it.
private lemma square_fac (F : C ⥤ D) (G : C' ⥤ D')
    (R : C ⥤ C') (S : D ⥤ D') [F.Additive] [G.Additive] [R.Additive] [S.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [R.PreservesKInjectiveComplexes] (e : F ⋙ S ≅ R ⋙ G)
    (K : HomotopyCategory C (.up ℤ)) :
    S.mapDerivedCategory.map (F.rightDerivedFunctorUnit.app K) ≫
        (derived_square F G R S e).hom.app (DerivedCategory.Qh.obj K) =
      S.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app K) ≫
        G.rightDerivedFunctorUnit.app ((R.mapHomotopyCategory (.up ℤ)).obj K) ≫
        G.rightDerivedFunctor.map (R.mapDerivedCategoryFactorsh.inv.app K) := by
  apply (cancel_epi (S.mapDerivedCategoryFactorsh.inv.app
    ((F.mapHomotopyCategory (.up ℤ)).obj K))).1
  simp only [← Category.assoc, ← comp_map_fac F S K]
  simp only [derived_square, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Category.assoc,
    Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app_assoc]
  simp only [Functor.rightDerivedFunctorNatIso, Functor.rightDerivedFunctorNatTrans]
  erw [Functor.rightDerivedNatTrans_app_assoc]
  have hc : (R ⋙ G).rightDerivedFunctorUnit.app K ≫
      (Functor.rightDerivedFunctorCompIso R G).hom.app (DerivedCategory.Qh.obj K) =
      (Functor.rightDerivedFunctorCompUnit R G).app K := by
    simp [Functor.rightDerivedFunctorCompIso]
  simp only [Functor.whiskerRight_app]
  erw [reassoc_of% hc]
  rw [comp_unit_app]
  simp only [Category.assoc, ← Functor.map_comp]
  have hr := congr_app R.rightDerivedFunctorIsoMapDerivedCategory_hom_fac K
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hr
  rw [hr]

omit [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D] in
private lemma factorsh_hom (H : C ⥤ D) [H.Additive]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H] (P : CochainComplex C ℤ) :
    H.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ _).obj P) =
      H.mapDerivedCategoryFactors.hom.app P := by
  have h := H.mapDerivedCategoryFactorsh_hom_app P
  change H.mapDerivedCategoryFactorsh.hom.app _ =
    H.mapDerivedCategory.map (𝟙 _) ≫ H.mapDerivedCategoryFactors.hom.app P ≫
      𝟙 _ ≫ DerivedCategory.Qh.map (𝟙 _) at h
  erw [H.mapDerivedCategory.map_id, DerivedCategory.Qh.map_id] at h
  repeat erw [Category.comp_id] at h
  erw [Category.id_comp] at h
  exact h

omit [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D] in
private lemma factorsh_inv (H : C ⥤ D) [H.Additive]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H] (P : CochainComplex C ℤ) :
    H.mapDerivedCategoryFactorsh.inv.app ((HomotopyCategory.quotient _ _).obj P) =
      H.mapDerivedCategoryFactors.inv.app P := by
  exact (Iso.inv_eq_inv
    (H.mapDerivedCategoryFactorsh.app ((HomotopyCategory.quotient _ _).obj P))
    (H.mapDerivedCategoryFactors.app P)).2 (factorsh_hom H P)

omit [Abelian.HasKInjectiveResolutions D] in
private lemma unitQ_homotopy (H : C ⥤ D) [H.Additive] (P : CochainComplex C ℤ) :
    H.rightDerivedFunctorUnitQ P =
      H.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj P) := by
  change 𝟙 _ ≫ H.rightDerivedFunctorUnit.app _ ≫
    H.rightDerivedFunctor.map (𝟙 _) = _
  erw [H.rightDerivedFunctor.map_id, Category.id_comp, Category.comp_id]
  rfl

omit [Abelian.HasKInjectiveResolutions D] in
/-- The exact restriction square satisfies its full canonical cochain-unit equation.

Source: Stacks Project Tag 070G, uniqueness and composition of right-derived functors;
blueprint coefficient changes, paragraph (2), deriving the restriction square.
(blueprint: lem-right-derived-exact-restriction-normalization).

Proof: cancel the inverse exact-functor comparison. The defining equations for the
composition comparison and the comparison of naturally isomorphic functors reduce the
homotopy-category square to the two right-derived units. The exact functor's comparison
unit supplies the remaining factor. On a cochain complex, the quotient comparison
components and the homotopy-factor comparison components are identities. Substitute
these into the homotopy equation, then cancel the inverse/direct exact-functor factors
inside the second right-derived functor. No computation hypothesis on the complex is used. -/
theorem rightDerivedExactRestriction_normalization (F : C ⥤ D) (G : C' ⥤ D')
    (R : C ⥤ C') (S : D ⥤ D') [F.Additive] [G.Additive] [R.Additive] [S.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [R.PreservesKInjectiveComplexes] (e : F ⋙ S ≅ R ⋙ G)
    (P : CochainComplex C ℤ) :
    S.mapDerivedCategory.map (F.rightDerivedFunctorUnitQ P) ≫
        ((Functor.rightDerivedFunctorCompMapDerivedCategoryIso F S).symm ≪≫
          Functor.rightDerivedFunctorNatIso e ≪≫ Functor.rightDerivedFunctorCompIso R G ≪≫
          Functor.isoWhiskerRight R.rightDerivedFunctorIsoMapDerivedCategory
            G.rightDerivedFunctor).hom.app (DerivedCategory.Q.obj P) ≫
        G.rightDerivedFunctor.map (R.mapDerivedCategoryFactors.hom.app P) =
      S.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app P) ≫
        G.rightDerivedFunctorUnitQ ((R.mapHomologicalComplex (.up ℤ)).obj P) := by
  have hn := square_fac F G R S e ((HomotopyCategory.quotient _ (.up ℤ)).obj P)
  have hn' : S.mapDerivedCategory.map (F.rightDerivedFunctorUnitQ P) ≫
      (derived_square F G R S e).hom.app (DerivedCategory.Q.obj P) =
    S.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app P) ≫
      G.rightDerivedFunctorUnitQ ((R.mapHomologicalComplex (.up ℤ)).obj P) ≫
      G.rightDerivedFunctor.map (R.mapDerivedCategoryFactors.inv.app P) := by
    erw [factorsh_hom S ((F.mapHomologicalComplex (.up ℤ)).obj P), factorsh_inv R P] at hn
    simp only [unitQ_homotopy]
    convert (config := { transparency := .all }) hn using 1 <;> rfl
  erw [reassoc_of% hn']
  erw [← G.rightDerivedFunctor.map_comp, Iso.inv_hom_id_app,
    G.rightDerivedFunctor.map_id, Category.comp_id]

end

end ProofHelpers
end CategoryTheory

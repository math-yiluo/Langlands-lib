/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.SectionDerivedRealization
import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionMateTranspose
import WeilConjectures.CategoryTheory.DerivedExactMate
import WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import WeilConjectures.CategoryTheory.EquivalenceAdjunctionComparison
import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction

/-! # Normalization of derived section push-pull

Source: Stacks Project, `derived.tex`, Tags 09T5 and 08BJ, and
`sites-cohomology.tex`, Tags 07A6 and 0FPI
(auxiliary; not a blueprint node).

The statement records the comparison of the fixed internal module operations with
the section-module operations after passage to derived categories.  All functors,
equivalences, and comparison maps are the constructions imported from the preceding
section-module modules.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.all false
set_option linter.unusedVariables false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

private theorem qh_map_quotient
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    {P Q : CochainComplex A ℤ} (t : P ⟶ Q) :
    DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map t) =
      DerivedCategory.Q.map t := by
  have h := DerivedCategory.quotientCompQhIso_hom_naturality t
  change DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map t) ≫
      𝟙 _ = 𝟙 _ ≫ DerivedCategory.Q.map t at h
  simpa only [Category.id_comp, Category.comp_id] using h

private theorem factorsh_quotient
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (P : CochainComplex A ℤ) :
    F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) =
      F.mapDerivedCategoryFactors.hom.app P := by
  rw [Functor.mapDerivedCategoryFactorsh_hom_app]
  simp only [DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv,
    Quotient.lift.isLift_hom]
  erw [CategoryTheory.Functor.map_id, DerivedCategory.Qh.map_id]
  erw [Category.comp_id, Category.comp_id, Category.id_comp]

private theorem counit_quotient_transport
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] (LF : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Qh ⋙ LF ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (P : CochainComplex A ℤ) :
    LF.map ((DerivedCategory.quotientCompQhIso A).inv.app P) ≫
        ε.app ((HomotopyCategory.quotient A (.up ℤ)).obj P) ≫
        DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
        (DerivedCategory.quotientCompQhIso B).hom.app
          ((F.mapHomologicalComplex (.up ℤ)).obj P) =
      ε.app ((HomotopyCategory.quotient A (.up ℤ)).obj P) := by
  simp only [DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv,
    Quotient.lift.isLift_hom]
  erw [LF.map_id, DerivedCategory.Qh.map_id]
  erw [Category.comp_id, Category.comp_id, Category.id_comp]

private theorem unit_quotient_transport
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] (RF : DerivedCategory A ⥤ DerivedCategory B)
    (η : F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    (P : CochainComplex A ℤ) :
    (DerivedCategory.quotientCompQhIso B).inv.app
        ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors (.up ℤ)).inv.app P) ≫
        η.app ((HomotopyCategory.quotient A (.up ℤ)).obj P) ≫
        RF.map ((DerivedCategory.quotientCompQhIso A).hom.app P) =
      η.app ((HomotopyCategory.quotient A (.up ℤ)).obj P) := by
  simp only [DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv,
    Quotient.lift.isLift_hom]
  erw [DerivedCategory.Qh.map_id, RF.map_id]
  erw [Category.id_comp, Category.id_comp, Category.comp_id]

private theorem squareFactors
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (K : C ⥤ D)
    [F.Additive] [G.Additive] [H.Additive] [K.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits K] [PreservesFiniteColimits K]
    (e : F ⋙ G ≅ H ⋙ K) (P : CochainComplex A ℤ) :
    (Functor.mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Q.obj P) ≫
        K.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app P) ≫
          K.mapDerivedCategoryFactors.hom.app
            ((H.mapHomologicalComplex (.up ℤ)).obj P) =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app P) := by
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors,
    Functor.mapDerivedCategoryNatIso_fac]
  rw [← cancel_epi ((Functor.mapDerivedCategoryCompIso F G).inv.app
    (DerivedCategory.Q.obj P))]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors_assoc]
  rfl

private theorem squareFactorsh
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (K : C ⥤ D)
    [F.Additive] [G.Additive] [H.Additive] [K.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits K] [PreservesFiniteColimits K]
    (e : F ⋙ G ≅ H ⋙ K) (P : HomotopyCategory A (.up ℤ)) :
    (Functor.mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Qh.obj P) ≫
        K.mapDerivedCategory.map (H.mapDerivedCategoryFactorsh.hom.app P) ≫
          K.mapDerivedCategoryFactorsh.hom.app
            ((H.mapHomotopyCategory (.up ℤ)).obj P) =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app P) ≫
        G.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj P) ≫
          DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app P) := by
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factorsh,
    Functor.mapDerivedCategoryNatIso_fach]
  rw [← cancel_epi ((Functor.mapDerivedCategoryCompIso F G).inv.app
    (DerivedCategory.Qh.obj P))]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factorsh_assoc]

private theorem pullSquareFactors
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (K : C ⥤ D)
    [F.Additive] [G.Additive] [H.Additive] [K.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits K] [PreservesFiniteColimits K]
    (LF : DerivedCategory A ⥤ DerivedCategory B) (c : LF ≅ F.mapDerivedCategory)
    (ε : DerivedCategory.Qh ⋙ LF ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (hc : Functor.whiskerLeft DerivedCategory.Qh c.hom ≫
      F.mapDerivedCategoryFactorsh.hom = ε)
    (e : F ⋙ G ≅ H ⋙ K) (P : CochainComplex A ℤ) :
    (Functor.isoWhiskerRight c G.mapDerivedCategory ≪≫
      Functor.mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Q.obj P) ≫
      K.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app P) ≫
      K.mapDerivedCategoryFactors.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj P) =
    G.mapDerivedCategory.map (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
      G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app P) := by
  have h := squareFactors F G H K e P
  have hε := NatTrans.congr_app hc ((HomotopyCategory.quotient _ (.up ℤ)).obj P)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, factorsh_quotient] at hε
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Category.assoc, Iso.symm_hom]
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc] at h
  erw [h, ← Functor.map_comp_assoc, hε]

section RightSquare

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory C] [HasDerivedCategory D]
  [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions B]
  [Abelian.HasKInjectiveResolutions C]
  (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (K : C ⥤ D)
  [F.Additive] [G.Additive] [H.Additive] [K.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [H.PreservesKInjectiveComplexes]

private def rightSquareIso (e : F ⋙ G ≅ H ⋙ K) :
    F.rightDerivedFunctor ⋙ G.mapDerivedCategory ≅
      H.mapDerivedCategory ⋙ K.rightDerivedFunctor :=
  (Functor.rightDerivedFunctorCompMapDerivedCategoryIso F G).symm ≪≫
    Functor.rightDerivedFunctorNatIso e ≪≫
    Functor.rightDerivedFunctorCompIso H K ≪≫
    Functor.isoWhiskerRight H.rightDerivedFunctorIsoMapDerivedCategory K.rightDerivedFunctor

private theorem rightSquareFactorsh (e : F ⋙ G ≅ H ⋙ K)
    (P : HomotopyCategory A (.up ℤ)) :
    G.mapDerivedCategory.map (F.rightDerivedFunctorUnit.app P) ≫
        (rightSquareIso F G H K e).hom.app (DerivedCategory.Qh.obj P) ≫
          K.rightDerivedFunctor.map (H.mapDerivedCategoryFactorsh.hom.app P) =
      G.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj P) ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app P) ≫
          K.rightDerivedFunctorUnit.app ((H.mapHomotopyCategory (.up ℤ)).obj P) := by
  have h₄ := NatTrans.congr_app H.rightDerivedFunctorIsoMapDerivedCategory_hom_fac P
  have hi (R : A ⥤ B) (S : B ⥤ D) [R.Additive] [S.Additive] :
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (R ⋙ S)) (.up ℤ)).inv.app P = 𝟙 _ := by
    rw [← cancel_epi ((Functor.mapHomotopyCategoryCompIso
      (Iso.refl (R ⋙ S)) (.up ℤ)).hom.app P), Iso.hom_inv_id_app,
      Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.comp_id]
  have hi' : (Functor.mapHomotopyCategoryCompIso
      (Iso.refl (H ⋙ K)) (.up ℤ)).inv.app P = 𝟙 _ := by
    rw [← cancel_epi ((Functor.mapHomotopyCategoryCompIso
      (Iso.refl (H ⋙ K)) (.up ℤ)).hom.app P), Iso.hom_inv_id_app,
      Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.comp_id]
  have hstart : G.mapDerivedCategory.map (F.rightDerivedFunctorUnit.app P) =
      G.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj P) ≫
        (Functor.rightDerivedFunctorCompMapDerivedCategoryUnit F G).app P := by
    simp only [Functor.rightDerivedFunctorCompMapDerivedCategoryUnit, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.associator_inv_app, hi F G, CategoryTheory.Functor.map_id, Category.id_comp,
      Category.comp_id, Category.assoc]
    erw [Category.id_comp, Iso.hom_inv_id_app_assoc]
  rw [hstart]
  simp only [rightSquareIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Category.assoc,
    Functor.rightDerivedFunctorCompMapDerivedCategoryIso,
    Functor.rightDerivedFunctorCompIso, Functor.rightDerivedUnique,
    Functor.rightDerivedNatIso, Functor.rightDerivedFunctorNatIso,
    Functor.rightDerivedFunctorNatTrans, Iso.refl_inv, Iso.refl_hom]
  rw [Functor.rightDerivedNatTrans_app_assoc]
  simp only [NatTrans.id_app, Category.id_comp]
  rw [Functor.rightDerivedNatTrans_app_assoc]
  simp only [Functor.whiskerRight_app, Category.assoc]
  rw [Functor.rightDerivedNatTrans_app_assoc]
  simp only [NatTrans.id_app, Category.id_comp]
  simp only [Functor.rightDerivedFunctorCompUnit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, hi', CategoryTheory.Functor.map_id, Category.id_comp,
    Category.comp_id, Category.assoc, ← Functor.map_comp]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h₄
  erw [Category.id_comp]
  have hc : H.rightDerivedFunctorUnit.app P ≫
      H.rightDerivedFunctorIsoMapDerivedCategory.hom.app (DerivedCategory.Qh.obj P) ≫
        H.mapDerivedCategoryFactorsh.hom.app P = 𝟙 _ := by
    rw [← Category.assoc, h₄, Iso.inv_hom_id_app]
  erw [hc, K.rightDerivedFunctor.map_id, Category.comp_id]

private theorem rightSquareStart (P : HomotopyCategory A (.up ℤ)) :
    G.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj P) ≫
      (Functor.rightDerivedFunctorCompMapDerivedCategoryUnit F G).app P =
        G.mapDerivedCategory.map (F.rightDerivedFunctorUnit.app P) := by
  have hi : (Functor.mapHomotopyCategoryCompIso
      (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app P = 𝟙 _ := by
    rw [← cancel_epi ((Functor.mapHomotopyCategoryCompIso
      (Iso.refl (F ⋙ G)) (.up ℤ)).hom.app P), Iso.hom_inv_id_app,
      Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.comp_id]
  simp only [Functor.rightDerivedFunctorCompMapDerivedCategoryUnit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, hi, CategoryTheory.Functor.map_id, Category.id_comp,
    Category.comp_id, Category.assoc]
  erw [Category.id_comp, Iso.hom_inv_id_app_assoc]

private theorem rightSquareFactors (e : F ⋙ G ≅ H ⋙ K)
    (P : CochainComplex A ℤ) :
    G.mapDerivedCategory.map (F.rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
      (rightSquareIso F G H K e).hom.app (DerivedCategory.Q.obj P) ≫
        K.rightDerivedFunctor.map (H.mapDerivedCategoryFactors.hom.app P) =
    G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app P) ≫
        K.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj
          ((H.mapHomologicalComplex (.up ℤ)).obj P)) := by
  have h := rightSquareFactorsh F G H K e
    ((HomotopyCategory.quotient _ (.up ℤ)).obj P)
  have hF : ((F.mapHomotopyCategory (.up ℤ)).obj
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) =
        (HomotopyCategory.quotient _ (.up ℤ)).obj
          ((F.mapHomologicalComplex (.up ℤ)).obj P) := rfl
  have hH : ((H.mapHomotopyCategory (.up ℤ)).obj
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) =
        (HomotopyCategory.quotient _ (.up ℤ)).obj
          ((H.mapHomologicalComplex (.up ℤ)).obj P) := rfl
  simp only [Functor.mapHomotopyCategory_obj, HomotopyCategory.quotient_obj_as] at h
  simp only [factorsh_quotient] at h
  have ht : (NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P) =
      (HomotopyCategory.quotient _ (.up ℤ)).map
        ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app P) := rfl
  rw [ht, qh_map_quotient] at h
  exact h

end RightSquare

section MateSquare

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory C] [HasDerivedCategory D]
  [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions B]
  [Abelian.HasKInjectiveResolutions C]
  {L : B ⥤ A} {R : A ⥤ B} {L' : D ⥤ C} {R' : C ⥤ D}
  (G : B ⥤ D) (H : A ⥤ C)
  [L.Additive] [R.Additive] [L'.Additive] [R'.Additive]
  [G.Additive] [H.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [H.PreservesKInjectiveComplexes]

private theorem squareSymm (e : L ⋙ H ≅ G ⋙ L') :
    Functor.mapDerivedCategorySquareIso e.symm =
      (Functor.mapDerivedCategorySquareIso e).symm := by
  apply Iso.ext
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, Functor.mapDerivedCategoryNatIso_symm, Category.assoc]

private theorem rightSquareMate (a : L ⊣ R) (b : L' ⊣ R')
    (e : L ⋙ H ≅ G ⋙ L') (r : R ⋙ G ≅ H ⋙ R')
    (hm : (mateEquiv a b e.inv) = r.hom) :
    (mateEquiv a.mapDerivedCategoryRightDerivedAdjunction
      b.mapDerivedCategoryRightDerivedAdjunction
        (Functor.mapDerivedCategorySquareIso e).inv) =
      (rightSquareIso R G H R' r).hom := by
  have hf (P : HomotopyCategory B (.up ℤ)) :=
    squareFactorsh G L' L H e.symm P
  simp only [squareSymm, Iso.symm_hom] at hf
  apply (R.rightDerivedFunctor ⋙ G.mapDerivedCategory).rightDerived_ext
    (Functor.rightDerivedFunctorCompMapDerivedCategoryUnit R G)
    (HomotopyCategory.quasiIso A (.up ℤ))
  ext P
  apply (cancel_epi (G.mapDerivedCategoryFactorsh.hom.app
    ((R.mapHomotopyCategory (.up ℤ)).obj P))).mp
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, ← Category.assoc,
    rightSquareStart]
  have h := a.derivedExact_mateEquiv_app_fac b e.inv
    (Functor.mapDerivedCategorySquareIso e).inv hf P
  rw [hm] at h
  have hr := rightSquareFactorsh R G H R' r P
  apply (cancel_mono (R'.rightDerivedFunctor.map
    (H.mapDerivedCategoryFactorsh.hom.app P))).mp
  simp only [Category.assoc] at h hr ⊢
  rw [reassoc_of% h, hr]
  simp only [← Functor.map_comp, Iso.inv_hom_id_app]
  erw [R'.rightDerivedFunctor.map_id, Category.comp_id]

end MateSquare

private theorem transportSquare_comp
    {A B C Ab Bb Cb : Type*} [Category A] [Category B] [Category C]
    [Category Ab] [Category Bb] [Category Cb]
    (U : A ⥤ Ab) (V : B ⥤ Bb) (W : C ⥤ Cb)
    {F F' : A ⥤ B} {K K' : B ⥤ C} {T T' : A ⥤ C}
    {Fb : Ab ⥤ Bb} {Kb : Bb ⥤ Cb} {Tb : Ab ⥤ Cb}
    (p : F ⋙ V ≅ U ⋙ Fb) (q : K ⋙ W ≅ V ⋙ Kb) (r : T ⋙ W ≅ U ⋙ Tb)
    (d : T ≅ F ⋙ K) (db : Tb ≅ Fb ⋙ Kb)
    (cF : F' ≅ F) (cK : K' ≅ K) (cT : T' ≅ T)
    (hd : ∀ X, r.hom.app X ≫ db.hom.app (U.obj X) =
      W.map (d.hom.app X) ≫ q.hom.app (F.obj X) ≫ Kb.map (p.hom.app X))
    (M : A) :
    (Functor.isoWhiskerRight cT W ≪≫ r).hom.app M ≫ db.hom.app (U.obj M) =
      W.map ((cT ≪≫ d ≪≫ Functor.isoWhiskerRight cF.symm K ≪≫
        Functor.isoWhiskerLeft F' cK.symm).hom.app M) ≫
        (Functor.isoWhiskerRight cK W ≪≫ q).hom.app (F'.obj M) ≫
        Kb.map ((Functor.isoWhiskerRight cF V ≪≫ p).hom.app M) := by
  have hn := q.hom.naturality (cF.inv.app M)
  simp only [Functor.comp_map] at hn
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.map_comp, Category.assoc]
  have hK : W.map (cK.inv.app (F'.obj M)) ≫
      W.map (cK.hom.app (F'.obj M)) = 𝟙 _ := by
    rw [← W.map_comp, Iso.inv_hom_id_app, W.map_id]
  rw [reassoc_of% hK]
  rw [reassoc_of% hn]
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  have hF : V.map (cF.inv.app M) ≫ V.map (cF.hom.app M) ≫ p.hom.app M =
      p.hom.app M := by
    rw [← V.map_comp_assoc, Iso.inv_hom_id_app, V.map_id, Category.id_comp]
  rw [hF]
  exact congrArg (fun t ↦ W.map (cT.hom.app M) ≫ t) (hd M)

private theorem normalizedMate_hom
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {Lb : C ⥤ D} {Rb : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D}
    (a : L ⊣ R) (b : Lb ⊣ Rb)
    (e : L ⋙ H ≅ G ⋙ Lb) (r : R ⋙ G ≅ H ⋙ Rb)
    (hm : (mateEquiv a b e.inv) = r.hom)
    (M : A) (N : B) (q : L.obj M ⟶ N) :
    b.homEquiv _ _ (e.inv.app M ≫ H.map q) = G.map (a.homEquiv _ _ q) ≫ r.hom.app N := by
  have he : ((mateEquiv a b).symm r.hom) = e.inv := by
    rw [← hm]
    exact (mateEquiv a b).symm_apply_apply e.inv
  have h := adjunctionMate_transpose a b r.hom M N q
  change b.homEquiv _ _ (((mateEquiv a b).symm r.hom).app M ≫ H.map q) = _ at h
  rw [he] at h
  exact h

private theorem normalizedMate_unit
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {Lb : C ⥤ D} {Rb : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D}
    (a : L ⊣ R) (b : Lb ⊣ Rb)
    (e : L ⋙ H ≅ G ⋙ Lb) (r : R ⋙ G ≅ H ⋙ Rb)
    (hm : (mateEquiv a b e.inv) = r.hom) (M : A) :
    b.unit.app (G.obj M) = G.map (a.unit.app M) ≫ r.hom.app (L.obj M) ≫
      Rb.map (e.hom.app M) := by
  have h := unit_mateEquiv a b e.inv M
  change G.map (a.unit.app M) ≫ (mateEquiv a b e.inv).app (L.obj M) = _ at h
  rw [hm] at h
  apply (cancel_mono (Rb.map (e.inv.app M))).mp
  simp only [Category.assoc, ← Rb.map_comp, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  exact h.symm

private theorem normalizedMate_counit
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {Lb : C ⥤ D} {Rb : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D}
    (a : L ⊣ R) (b : Lb ⊣ Rb)
    (e : L ⋙ H ≅ G ⋙ Lb) (r : R ⋙ G ≅ H ⋙ Rb)
    (hm : (mateEquiv a b e.inv) = r.hom) (N : B) :
    b.counit.app (H.obj N) = Lb.map (r.inv.app N) ≫ e.inv.app (R.obj N) ≫
      H.map (a.counit.app N) := by
  have h := mateEquiv_counit a b e.inv N
  change Lb.map ((mateEquiv a b e.inv).app N) ≫ _ = _ at h
  rw [hm] at h
  apply (cancel_epi (Lb.map (r.hom.app N))).mp
  simp only [← Category.assoc, ← Lb.map_comp, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  exact h

private theorem mate_transport_left
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L LF : A ⥤ B} {R : B ⥤ A} {Lb : C ⥤ D} {Rb : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D}
    (a : L ⊣ R) (b : Lb ⊣ Rb) (c : LF ≅ L) (e : L ⋙ H ≅ G ⋙ Lb) :
    (mateEquiv (a.ofNatIsoLeft c.symm) b
      (Functor.isoWhiskerRight c H ≪≫ e).inv) =
      (mateEquiv a b e.inv) := by
  have ht := conjugateEquiv_mateEquiv_vcomp (a.ofNatIsoLeft c.symm) a b c.inv e.inv
  have he : TwoSquare.whiskerLeft (TwoSquare.mk _ _ _ _ e.inv) c.inv =
      (Functor.isoWhiskerRight c H ≪≫ e).inv := by
    ext M
    rfl
  have hid : conjugateEquiv (a.ofNatIsoLeft c.symm) a c.inv = 𝟙 R := by
    ext N
    simp only [conjugateEquiv_apply_app, Adjunction.ofNatIsoLeft_counit,
      Adjunction.ofNatIsoLeft_unit, Iso.symm_inv, NatTrans.comp_app,
      Functor.whiskerLeft_app, Category.assoc, ← R.map_comp,
      Iso.inv_hom_id_app, Category.comp_id]
    simp
  rw [he, hid] at ht
  simpa [TwoSquare.whiskerTop] using ht

namespace AlgebraicGeometry.ProEtale.ModuleRingedComparison

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  [∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)]

/-- The existing internal derived adjunction with its two functor types fixed explicitly.
Source: Stacks 09T5 and 07A6
(auxiliary; not a blueprint node). -/
def normalizationInternalAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    internalDerivedPullback Λ f ⊣ internalDerivedPushforward Λ f :=
  CondensedRing.derivedUpperStarLowerStarAdjunction Λ f

private theorem internalPushComp_underlying {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (M : internalModules Λ X) :
    ((CondensedRing.lowerStarComp Λ f g).hom.app M).hom =
      (ProEtale.lowerStarComp Ab.{u + 1} f g).hom.app M.X := by
  simp only [Functor.comp_obj, CondensedRing.lowerStarComp, Functor.isoWhiskerLeft_trans,
    Functor.isoWhiskerLeft_twice, Functor.mapModCompIso,
    CondensedRing.comapCondensedPushforwardHomComp, Iso.trans_assoc,
    Iso.self_symm_id_assoc, Iso.trans_hom, Functor.isoWhiskerLeft_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Functor.associator_inv_app, Functor.whiskerRight_app,
    NatIso.ofComponents_hom_app, Category.id_comp, Mod.comp_hom', Mod.id_hom',
    Mod.comap_map_hom, Functor.mapModComapIso_hom_app_hom, Mod.comapComp_inv_app_hom,
    Mod.isoMk_hom_hom, asIso_hom, Mod.comapCongr_hom_app_hom]
  erw [Category.id_comp, Category.id_comp, Category.id_comp, Category.id_comp,
    Category.comp_id]

private theorem pushComparison_underlying {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : internalModules Λ X) :
    (SheafOfModules.toSheaf _).map ((pushComparison Λ f).hom.app M) =
      𝟙 ((ProEtale.lowerStar Ab.{u + 1} f).obj M.X) := by
  ext V m
  exact (InternalModuleOperations.lowerComparison_existsUnique Λ f).exists.choose_spec M V m

private theorem sectionMap_underlying {T : Scheme.{u}} {M N : internalModules Λ T}
    (q : M ⟶ N) :
    (SheafOfModules.toSheaf _).map ((equivalence Λ T).functor.map q) = q.hom := rfl

private theorem pushforward_underlying {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : modules Λ X} (q : M ⟶ N) :
    (SheafOfModules.toSheaf _).map ((pushforward Λ f).map q) =
      (ProEtale.lowerStar Ab.{u + 1} f).map ((SheafOfModules.toSheaf _).map q) := rfl

private theorem pushComp_underlying {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : modules Λ X) :
    (SheafOfModules.toSheaf _).map ((pushforwardComposition Λ f g).hom.app M) =
      (ProEtale.lowerStarComp Ab.{u + 1} f g).hom.app
        ((SheafOfModules.toSheaf _).obj M) := by
  ext V m
  exact (InternalModuleOperations.lowerComp_existsUnique Λ f g).exists.choose_spec M V m

private theorem sectionObject_underlying {T : Scheme.{u}} (M : internalModules Λ T) :
    (SheafOfModules.toSheaf _).obj ((equivalence Λ T).functor.obj M) = M.X := rfl

private theorem sectionPushComp_underlying {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (M : internalModules Λ X) :
    (SheafOfModules.toSheaf _).map
        ((pushforwardComposition Λ f g).hom.app ((equivalence Λ X).functor.obj M)) =
      (ProEtale.lowerStarComp Ab.{u + 1} f g).hom.app M.X := by
  have h := pushComp_underlying Λ f g ((equivalence Λ X).functor.obj M)
  simpa only [sectionObject_underlying] using h

private theorem ordinaryPushComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : internalModules Λ X) :
    (pushComparison Λ g).hom.app ((CondensedRing.lowerStar Λ f).obj M) ≫
      (pushforward Λ g).map ((pushComparison Λ f).hom.app M) ≫
      (pushforwardComposition Λ f g).hom.app ((equivalence Λ X).functor.obj M) =
    (equivalence Λ Z).functor.map ((CondensedRing.lowerStarComp Λ f g).hom.app M) ≫
      (pushComparison Λ (f ≫ g)).hom.app M := by
  apply (SheafOfModules.toSheaf _).map_injective
  simp only [CategoryTheory.Functor.map_comp, pushComparison_underlying,
    sectionMap_underlying, pushforward_underlying, sectionPushComp_underlying,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id,
    internalPushComp_underlying]
  have h := sectionPushComp_underlying Λ f g M
  convert h using 1 <;>
    first | rfl | simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

private theorem ordinaryPullComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : internalModules Λ Z) :
    (equivalence Λ X).functor.map ((CondensedRing.upperStarComp Λ f g).hom.app M) ≫
      (pullComparison Λ f).hom.app ((CondensedRing.upperStar Λ g).obj M) ≫
      (pullback Λ f).map ((pullComparison Λ g).hom.app M) =
    (pullComparison Λ (f ≫ g)).hom.app M ≫
      (pullbackComposition Λ f g).hom.app ((equivalence Λ Z).functor.obj M) := by
  have hi : conjugateEquiv (CondensedRing.upperStarLowerStarAdjunction Λ (f ≫ g))
      ((CondensedRing.upperStarLowerStarAdjunction Λ g).comp
        (CondensedRing.upperStarLowerStarAdjunction Λ f))
        (CondensedRing.upperStarComp Λ f g).inv =
          (CondensedRing.lowerStarComp Λ f g).inv := by
    exact congrArg Iso.hom ((conjugateIsoEquiv
      (CondensedRing.upperStarLowerStarAdjunction Λ (f ≫ g))
      ((CondensedRing.upperStarLowerStarAdjunction Λ g).comp
        (CondensedRing.upperStarLowerStarAdjunction Λ f))).apply_symm_apply
          (CondensedRing.lowerStarComp Λ f g).symm)
  have hs : conjugateEquiv (adjunction Λ (f ≫ g))
      ((adjunction Λ g).comp (adjunction Λ f)) (pullbackComposition Λ f g).inv =
        (pushforwardComposition Λ f g).inv := by
    exact congrArg Iso.hom ((conjugateIsoEquiv (adjunction Λ (f ≫ g))
      ((adjunction Λ g).comp (adjunction Λ f))).apply_symm_apply
        (pushforwardComposition Λ f g).symm)
  have h := equivalenceAdjunctionComparison_compositor
    (equivalence Λ Z) (equivalence Λ Y) (equivalence Λ X)
    (CondensedRing.upperStarLowerStarAdjunction Λ g)
    (CondensedRing.upperStarLowerStarAdjunction Λ f)
    (CondensedRing.upperStarLowerStarAdjunction Λ (f ≫ g))
    (adjunction Λ g) (adjunction Λ f) (adjunction Λ (f ≫ g))
    (pushComparison Λ g) (pushComparison Λ f) (pushComparison Λ (f ≫ g))
    (pullComparison Λ g) (pullComparison Λ f) (pullComparison Λ (f ≫ g))
    (InternalModuleOperations.upperComparison_existsUnique Λ g).exists.choose_spec
    (InternalModuleOperations.upperComparison_existsUnique Λ f).exists.choose_spec
    (InternalModuleOperations.upperComparison_existsUnique Λ (f ≫ g)).exists.choose_spec
    (CondensedRing.lowerStarComp Λ f g) (pushforwardComposition Λ f g)
    (ordinaryPushComp Λ f g) (CondensedRing.upperStarComp Λ f g).symm
    (pullbackComposition Λ f g).symm hi hs M
  apply (cancel_epi ((equivalence Λ X).functor.map
    ((CondensedRing.upperStarComp Λ f g).inv.app M))).mp
  simp only [← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [Iso.symm_hom] at h
  rw [h]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  erw [Category.comp_id]

private theorem comparison_conjugate_comp
    {A B C Ab Bb Cb : Type*} [Category A] [Category B] [Category C]
    [Category Ab] [Category Bb] [Category Cb]
    (U : A ⥤ Ab) (V : B ⥤ Bb) (W : C ⥤ Cb)
    {L : A ⥤ B} {R : B ⥤ A} {K : B ⥤ C} {S : C ⥤ B}
    {T : A ⥤ C} {Q : C ⥤ A}
    {Lb : Ab ⥤ Bb} {Rb : Bb ⥤ Ab} {Kb : Bb ⥤ Cb} {Sb : Cb ⥤ Bb}
    {Tb : Ab ⥤ Cb} {Qb : Cb ⥤ Ab}
    (a : L ⊣ R) (b : K ⊣ S) (c : T ⊣ Q)
    (ab : Lb ⊣ Rb) (bb : Kb ⊣ Sb) (cb : Tb ⊣ Qb)
    (p : L ⋙ V ≅ U ⋙ Lb) (q : K ⋙ W ≅ V ⋙ Kb) (r : T ⋙ W ≅ U ⋙ Tb)
    (pr : R ⋙ U ≅ V ⋙ Rb) (qr : S ⋙ V ≅ W ⋙ Sb) (rr : Q ⋙ U ≅ W ⋙ Qb)
    (hp : (mateEquiv a ab p.inv) = pr.hom)
    (hq : (mateEquiv b bb q.inv) = qr.hom)
    (hr : (mateEquiv c cb r.inv) = rr.hom)
    (d : T ≅ L ⋙ K) (db : Tb ≅ Lb ⋙ Kb)
    (hd : ∀ X, r.hom.app X ≫ db.hom.app (U.obj X) =
      W.map (d.hom.app X) ≫ q.hom.app (L.obj X) ≫ Kb.map (p.hom.app X))
    (N : C) :
    U.map ((conjugateEquiv (a.comp b) c d.hom).app N) ≫ rr.hom.app N =
      pr.hom.app (S.obj N) ≫ Rb.map (qr.hom.app N) ≫
        (conjugateEquiv (ab.comp bb) cb db.hom).app (W.obj N) := by
  let α : TwoSquare U (L ⋙ K) (Lb ⋙ Kb) W := TwoSquare.vComp p.inv q.inv
  have hm : mateEquiv (a.comp b) (ab.comp bb) α =
      TwoSquare.hComp qr.hom pr.hom := by
    rw [mateEquiv_hcomp]
    change TwoSquare.hComp ((mateEquiv b bb q.inv))
      ((mateEquiv a ab p.inv)) = _
    rw [hp, hq]
  have he : (TwoSquare.mk _ _ _ _ r.inv).whiskerLeft d.hom =
      α.whiskerRight db.hom := by
    ext X
    dsimp only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, α, TwoSquare.vComp,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app]
    try simp only [Category.id_comp, Category.comp_id]
    change r.inv.app X ≫ W.map (d.hom.app X) =
      db.hom.app (U.obj X) ≫ Kb.map (p.inv.app X) ≫ q.inv.app (L.obj X)
    apply (cancel_epi (r.hom.app X)).mp
    simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
    rw [hd X]
    simp only [Category.assoc, ← Kb.map_comp, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app, Category.comp_id]
    erw [Kb.map_id, Category.id_comp, Iso.hom_inv_id_app, Category.comp_id]
  have hl := conjugateEquiv_mateEquiv_vcomp (a.comp b) c cb d.hom r.inv
  have ht := mateEquiv_conjugateEquiv_vcomp (a.comp b) (ab.comp bb) cb α db.hom
  rw [he, ht, hm] at hl
  change mateEquiv c cb r.inv = rr.hom at hr
  rw [hr] at hl
  have hx := congrArg (fun t ↦ t.app N) hl
  simpa only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc] using hx.symm

private theorem internalAdjunction_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    normalizationInternalAdjunction Λ f =
      (Adjunction.mapDerivedCategoryRightDerivedAdjunction
        (CondensedRing.upperStarLowerStarAdjunction Λ f)).ofNatIsoLeft
        (CondensedRing.upperStar Λ f).leftDerivedFunctorIsoMapDerivedCategory.symm := by
  exact ((CondensedRing.upperStarLowerStarAdjunction Λ f).mapHomotopyCategory
    (.up ℤ)).derived_eq_ofNatIsoLeft
      (HomotopyCategory.quasiIso (internalModules Λ Y) (.up ℤ))
      (HomotopyCategory.quasiIso (internalModules Λ X) (.up ℤ))
      (CondensedRing.upperStar Λ f).leftDerivedFunctorCounit
      (CondensedRing.upperStar Λ f).mapDerivedCategoryFactorsh.hom
      (CondensedRing.lowerStar Λ f).rightDerivedFunctorUnit
      (CondensedRing.upperStar Λ f).leftDerivedFunctorIsoMapDerivedCategory
      (CondensedRing.upperStar Λ f).leftDerivedFunctorIsoMapDerivedCategory_hom_fac.symm

private theorem sectionAdjunction_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    derivedAdjunction Λ f = (adjunction Λ f).mapDerivedCategoryRightDerivedAdjunction := by
  have h := ((adjunction Λ f).mapHomotopyCategory (.up ℤ)).derived_eq_ofNatIsoLeft
    (HomotopyCategory.quasiIso (modules Λ Y) (.up ℤ))
    (HomotopyCategory.quasiIso (modules Λ X) (.up ℤ))
    (pullback Λ f).leftDerivedFunctorCounit
    (pullback Λ f).mapDerivedCategoryFactorsh.hom
    (pushforward Λ f).rightDerivedFunctorUnit
    (pullback Λ f).leftDerivedFunctorIsoMapDerivedCategory
    (pullback Λ f).leftDerivedFunctorIsoMapDerivedCategory_hom_fac.symm
  change (adjunction Λ f).derivedAdjunction =
    (adjunction Λ f).mapDerivedCategoryRightDerivedAdjunction.ofNatIsoLeft
      (pullback Λ f).leftDerivedFunctorIsoMapDerivedCategory.symm at h
  dsimp only [derivedAdjunction]
  rw [h]
  apply Adjunction.ext_counit
  ext N
  simp [Adjunction.ofNatIsoLeft_counit]

private theorem derivedPullComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : DerivedCategory (internalModules Λ Z)) :
    (derivedPullComparison Λ (f ≫ g)).hom.app M ≫
      (derivedPullbackComposition Λ f g).hom.app ((derivedEquivalence Λ Z).functor.obj M) =
    (derivedEquivalence Λ X).functor.map
      ((CondensedRing.leftDerivedUpperStarComp Λ f g).hom.app M) ≫
      (derivedPullComparison Λ f).hom.app ((internalDerivedPullback Λ g).obj M) ≫
      (derivedPullback Λ f).map ((derivedPullComparison Λ g).hom.app M) := by
  have h := Functor.mapDerivedCategorySquareIso_comp
    (CondensedRing.upperStar Λ g) (CondensedRing.upperStar Λ f)
    (CondensedRing.upperStar Λ (f ≫ g))
    (pullback Λ g) (pullback Λ f) (pullback Λ (f ≫ g))
    (equivalence Λ Z).functor (equivalence Λ Y).functor (equivalence Λ X).functor
    (pullComparison Λ g) (pullComparison Λ f) (pullComparison Λ (f ≫ g))
    (CondensedRing.upperStarComp Λ f g) (pullbackComposition Λ f g)
    (ordinaryPullComp Λ f g)
  have hd (N : DerivedCategory (internalModules Λ Z)) :=
    congrArg (fun e ↦ e.hom.app N) h
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id] at hd
  have ht := transportSquare_comp
    (derivedEquivalence Λ Z).functor (derivedEquivalence Λ Y).functor
    (derivedEquivalence Λ X).functor
    (Functor.mapDerivedCategorySquareIso (pullComparison Λ g))
    (Functor.mapDerivedCategorySquareIso (pullComparison Λ f))
    (Functor.mapDerivedCategorySquareIso (pullComparison Λ (f ≫ g)))
    (Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarComp Λ f g) ≪≫
      (Functor.mapDerivedCategoryCompIso (CondensedRing.upperStar Λ g)
        (CondensedRing.upperStar Λ f)).symm)
    (derivedPullbackComposition Λ f g)
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ g)
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ f)
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ (f ≫ g))
    (fun N ↦ (hd N).symm) M
  simpa only [derivedPullComparison, derivedEquivalence, Functor.asEquivalence,
    internalDerivedPullback, comparisonSource, derivedPullback,
    CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory,
    CondensedRing.leftDerivedUpperStarComp,
    Functor.leftDerivedFunctorNatIso,
    Functor.leftDerivedFunctorCompIso, Iso.trans_assoc, Iso.symm_hom, Iso.symm_inv,
    Iso.symm_self_id_assoc] using ht

private theorem derivedMate {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (mateEquiv (normalizationInternalAdjunction Λ f) (derivedAdjunction Λ f)
      (derivedPullComparison Λ f).inv) = (derivedPushComparison Λ f).hom := by
  rw [internalAdjunction_eq, sectionAdjunction_eq]
  exact (mate_transport_left
    (CondensedRing.upperStarLowerStarAdjunction Λ f).mapDerivedCategoryRightDerivedAdjunction
    (adjunction Λ f).mapDerivedCategoryRightDerivedAdjunction
    (CondensedRing.upperStar Λ f).leftDerivedFunctorIsoMapDerivedCategory
    (Functor.mapDerivedCategorySquareIso (pullComparison Λ f))).trans
      (rightSquareMate (equivalence Λ Y).functor (equivalence Λ X).functor
        (CondensedRing.upperStarLowerStarAdjunction Λ f) (adjunction Λ f)
        (pullComparison Λ f) (pushComparison Λ f)
        (InternalModuleOperations.upperComparison_existsUnique Λ f).exists.choose_spec)

/--
Source: Stacks Project, `derived.tex`, Tags 09T5 and 08BJ, and
`sites-cohomology.tex`, Tags 07A6 and 0FPI
(auxiliary; not a blueprint node).

Proof, following the eight steps of the node.
1. Use the derived equivalence instance for the fixed additive section equivalence.
2. The equivalence and its exact inverse preserve K-injectivity. The degreewise
   unit identifies the image under their composite with the original complex,
   proving reflection. Combine this with reflection of quasi-isomorphisms.
3. The factorization equations for exact derived squares give the left comparison
   equation. The right equation follows from the unit equations for right-derived
   composition, natural isomorphisms, and composition with an exact functor.
   Evaluate the homotopy equations at quotient complexes.
4. The universal derived-adjunction comparison identifies the independently
   constructed adjunctions with the exact-left/right-derived adjunctions. The
   exact-derived mate formula and right-derived uniqueness identify the mate of
   the specified left square with the specified right square. Transport along
   the internal left-derived/exact-derived isomorphism.
5. Apply the general mate-transposition identity for the Hom comparison. The unit
   and counit mate identities give the two remaining equations by cancellation.
6. The ordinary pushforward comparisons are identities on sections. The ordinary
   section compositor and internal compositor have the same geometric underlying
   sheaf map. The normalized adjunction-comparison compositor theorem then gives
   the ordinary pullback square.
7. Localize that square with the exact-square composition theorem. Transport along
   the three left-derived/exact-derived isomorphisms, using naturality to cancel
   adjacent inverse factors. The resulting compositor is the specified internal
   left-derived compositor.
8. Mate pasting for the inverse pullback squares and the mixed conjugate/mate
   pasting identities give precisely the specified right compositor equation.

-/
theorem sectionDerivedPushpullNormalization {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (derivedFunctor Λ X).IsEquivalence ∧
    (derivedFunctor Λ Y).IsEquivalence ∧
    (∀ T : Scheme.{u}, ∀ P : CochainComplex (internalModules Λ T) ℤ,
      CochainComplex.IsKInjective
          (((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj P) ↔
        P.IsKInjective) ∧
    (∀ (T : Scheme.{u}) (P I : CochainComplex (internalModules Λ T) ℤ) (i : P ⟶ I),
      (QuasiIso (((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).map i) ∧
        CochainComplex.IsKInjective
          (((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj I)) ↔
        (QuasiIso i ∧ I.IsKInjective)) ∧
    (∀ P : CochainComplex (internalModules Λ Y) ℤ,
      (derivedPullComparison Λ f).hom.app (DerivedCategory.Q.obj P) ≫
          (derivedPullback Λ f).map (sectionLocalizationComparison Λ Y P).hom ≫
          (pullback Λ f).mapDerivedCategoryFactors.hom.app
            (((equivalence Λ Y).functor.mapHomologicalComplex (.up ℤ)).obj P) =
        (derivedEquivalence Λ X).functor.map
            ((CondensedRing.upperStar Λ f).leftDerivedFunctor.map
                ((DerivedCategory.quotientCompQhIso (internalModules Λ Y)).inv.app P) ≫
              (CondensedRing.upperStar Λ f).leftDerivedFunctorCounit.app
                ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫
              DerivedCategory.Qh.map
                (((CondensedRing.upperStar Λ f).mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
              (DerivedCategory.quotientCompQhIso (internalModules Λ X)).hom.app
                (((CondensedRing.upperStar Λ f).mapHomologicalComplex (.up ℤ)).obj P)) ≫
          (sectionLocalizationComparison Λ X
            (((CondensedRing.upperStar Λ f).mapHomologicalComplex (.up ℤ)).obj P)).hom ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
            (pullComparison Λ f) (.up ℤ)).hom.app P)) ∧
    (∀ P : CochainComplex (internalModules Λ X) ℤ,
      (derivedEquivalence Λ Y).functor.map
          ((DerivedCategory.quotientCompQhIso (internalModules Λ Y)).inv.app
              (((CondensedRing.lowerStar Λ f).mapHomologicalComplex (.up ℤ)).obj P) ≫
            DerivedCategory.Qh.map
              (((CondensedRing.lowerStar Λ f).mapHomotopyCategoryFactors (.up ℤ)).inv.app P) ≫
            (CondensedRing.lowerStar Λ f).rightDerivedFunctorUnit.app
              ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫
            (CondensedRing.lowerStar Λ f).rightDerivedFunctor.map
              ((DerivedCategory.quotientCompQhIso (internalModules Λ X)).hom.app P)) ≫
          (derivedPushComparison Λ f).hom.app (DerivedCategory.Q.obj P) ≫
          (derivedPushforward Λ f).map (sectionLocalizationComparison Λ X P).hom =
        (sectionLocalizationComparison Λ Y
            (((CondensedRing.lowerStar Λ f).mapHomologicalComplex (.up ℤ)).obj P)).hom ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
            (pushComparison Λ f) (.up ℤ)).hom.app P) ≫
          (DerivedCategory.quotientCompQhIso (modules Λ Y)).inv.app
            (((pushforward Λ f).mapHomologicalComplex (.up ℤ)).obj
              (((equivalence Λ X).functor.mapHomologicalComplex (.up ℤ)).obj P)) ≫
          DerivedCategory.Qh.map
            (((pushforward Λ f).mapHomotopyCategoryFactors (.up ℤ)).inv.app
              (((equivalence Λ X).functor.mapHomologicalComplex (.up ℤ)).obj P)) ≫
          (pushforward Λ f).rightDerivedFunctorUnit.app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj
              (((equivalence Λ X).functor.mapHomologicalComplex (.up ℤ)).obj P)) ≫
          (pushforward Λ f).rightDerivedFunctor.map
            ((DerivedCategory.quotientCompQhIso (modules Λ X)).hom.app
              (((equivalence Λ X).functor.mapHomologicalComplex (.up ℤ)).obj P))) ∧
    (∀ (M : DerivedCategory (internalModules Λ Y))
      (N : DerivedCategory (internalModules Λ X))
      (q : (internalDerivedPullback Λ f).obj M ⟶ N),
      (derivedAdjunction Λ f).homEquiv _ _
          ((derivedPullComparison Λ f).inv.app M ≫
            (derivedEquivalence Λ X).functor.map q) =
        (derivedEquivalence Λ Y).functor.map
            ((normalizationInternalAdjunction Λ f).homEquiv _ _ q) ≫
          (derivedPushComparison Λ f).hom.app N) ∧
    (∀ (M : DerivedCategory (internalModules Λ Y)),
      (derivedAdjunction Λ f).unit.app ((derivedEquivalence Λ Y).functor.obj M) =
        (derivedEquivalence Λ Y).functor.map
            ((normalizationInternalAdjunction Λ f).unit.app M) ≫
          (derivedPushComparison Λ f).hom.app ((internalDerivedPullback Λ f).obj M) ≫
          (derivedPushforward Λ f).map ((derivedPullComparison Λ f).hom.app M)) ∧
    (∀ (N : DerivedCategory (internalModules Λ X)),
      (derivedAdjunction Λ f).counit.app ((derivedEquivalence Λ X).functor.obj N) =
        (derivedPullback Λ f).map ((derivedPushComparison Λ f).inv.app N) ≫
          (derivedPullComparison Λ f).inv.app ((internalDerivedPushforward Λ f).obj N) ≫
          (derivedEquivalence Λ X).functor.map
            ((normalizationInternalAdjunction Λ f).counit.app N)) ∧
    (∀ {Z : Scheme.{u}} (g : Y ⟶ Z)
      (M : DerivedCategory (internalModules Λ Z)),
      (derivedPullComparison Λ (f ≫ g)).hom.app M ≫
          (derivedPullbackComposition Λ f g).hom.app
            ((derivedEquivalence Λ Z).functor.obj M) =
        (derivedEquivalence Λ X).functor.map
            ((CondensedRing.leftDerivedUpperStarComp Λ f g).hom.app M) ≫
          (derivedPullComparison Λ f).hom.app
            ((internalDerivedPullback Λ g).obj M) ≫
          (derivedPullback Λ f).map
            ((derivedPullComparison Λ g).hom.app M)) ∧
    (∀ {Z : Scheme.{u}} (g : Y ⟶ Z)
      (N : DerivedCategory (internalModules Λ X)),
      (derivedEquivalence Λ Z).functor.map
          ((conjugateEquiv
            ((normalizationInternalAdjunction Λ g).comp
              (normalizationInternalAdjunction Λ f))
            (normalizationInternalAdjunction Λ (f ≫ g))
            (CondensedRing.leftDerivedUpperStarComp Λ f g).hom).app N) ≫
          (derivedPushComparison Λ (f ≫ g)).hom.app N =
        (derivedPushComparison Λ g).hom.app ((internalDerivedPushforward Λ f).obj N) ≫
          (derivedPushforward Λ g).map ((derivedPushComparison Λ f).hom.app N) ≫
          (conjugateEquiv ((derivedAdjunction Λ g).comp (derivedAdjunction Λ f))
            (derivedAdjunction Λ (f ≫ g)) (derivedPullbackComposition Λ f g).hom).app
              ((derivedEquivalence Λ X).functor.obj N)) := by
  have hK : ∀ (T : Scheme.{u}) (P : CochainComplex (internalModules Λ T) ℤ),
      CochainComplex.IsKInjective
        (((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj P) ↔
        P.IsKInjective := by
    intro T P
    constructor
    · intro h
      have h' : CochainComplex.IsKInjective
          (((equivalence Λ T).inverse.mapHomologicalComplex (.up ℤ)).obj
            (((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj P)) :=
        inferInstance
      exact (CochainComplex.isKInjective_iff_of_iso
        (((equivalence Λ T).mapHomologicalComplex (.up ℤ)).unitIso.symm.app P)).mp h'
    · intro h
      infer_instance
  refine ⟨inferInstance, inferInstance, hK, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro T P I i
    exact and_congr
      (HomologicalComplex.quasiIso_map_iff_of_preservesHomology i (equivalence Λ T).functor)
      (hK T I)
  · intro P
    conv_rhs =>
      lhs
      rw [counit_quotient_transport]
    exact pullSquareFactors (CondensedRing.upperStar Λ f) (equivalence Λ X).functor
      (equivalence Λ Y).functor (pullback Λ f)
      (CondensedRing.upperStar Λ f).leftDerivedFunctor
      (CondensedRing.upperStar Λ f).leftDerivedFunctorIsoMapDerivedCategory
      (CondensedRing.upperStar Λ f).leftDerivedFunctorCounit
      (CondensedRing.upperStar Λ f).leftDerivedFunctorIsoMapDerivedCategory_hom_fac
      (pullComparison Λ f) P
  · intro P
    conv_lhs =>
      lhs
      rw [unit_quotient_transport]
    conv_rhs =>
      rhs
      rhs
      rw [unit_quotient_transport]
    exact rightSquareFactors (CondensedRing.lowerStar Λ f) (equivalence Λ Y).functor
      (equivalence Λ X).functor (pushforward Λ f) (pushComparison Λ f) P
  · intro M N q
    exact normalizedMate_hom (normalizationInternalAdjunction Λ f) (derivedAdjunction Λ f)
      (derivedPullComparison Λ f) (derivedPushComparison Λ f) (derivedMate Λ f) M N q
  · intro M
    exact normalizedMate_unit (normalizationInternalAdjunction Λ f) (derivedAdjunction Λ f)
      (derivedPullComparison Λ f) (derivedPushComparison Λ f) (derivedMate Λ f) M
  · intro N
    exact normalizedMate_counit (normalizationInternalAdjunction Λ f) (derivedAdjunction Λ f)
      (derivedPullComparison Λ f) (derivedPushComparison Λ f) (derivedMate Λ f) N
  · intro Z g M
    exact derivedPullComp Λ f g M
  · intro Z g N
    exact comparison_conjugate_comp
      (derivedEquivalence Λ Z).functor (derivedEquivalence Λ Y).functor
      (derivedEquivalence Λ X).functor
      (normalizationInternalAdjunction Λ g) (normalizationInternalAdjunction Λ f)
      (normalizationInternalAdjunction Λ (f ≫ g))
      (derivedAdjunction Λ g) (derivedAdjunction Λ f) (derivedAdjunction Λ (f ≫ g))
      (derivedPullComparison Λ g) (derivedPullComparison Λ f)
      (derivedPullComparison Λ (f ≫ g))
      (derivedPushComparison Λ g) (derivedPushComparison Λ f)
      (derivedPushComparison Λ (f ≫ g))
      (derivedMate Λ g) (derivedMate Λ f) (derivedMate Λ (f ≫ g))
      (CondensedRing.leftDerivedUpperStarComp Λ f g) (derivedPullbackComposition Λ f g)
      (derivedPullComp Λ f g) N

end AlgebraicGeometry.ProEtale.ModuleRingedComparison

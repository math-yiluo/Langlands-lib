/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Shift.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor

/-!
# Naturality of normalized scalar reduction boundaries

The quotient and Kummer identifications are characterized by adjunction units.
Their naturality, and the naturality of the resulting degree-two boundary, are formal
consequences of the exact right-adjoint square and its shift-compatible derived mate.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
section
variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C] [HasDerivedCategory D]
  (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (I : C ⥤ D)
  [F.Additive] [G.Additive] [H.Additive] [I.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits I] [PreservesFiniteColimits I]
private theorem square_factors (e : F ⋙ G ≅ H ⋙ I) (K : CochainComplex A ℤ) :
    (CategoryTheory.Functor.mapDerivedCategorySquareIso e).hom.app
        (DerivedCategory.Q.obj K) ≫
      I.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app K) ≫
      I.mapDerivedCategoryFactors.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj K) =
    G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
      G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app K) := by
  simp only [CategoryTheory.Functor.mapDerivedCategorySquareIso, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [CategoryTheory.Functor.mapDerivedCategoryCompIso_hom_app_factors,
    CategoryTheory.Functor.mapDerivedCategoryNatIso_fac]
  rw [← CategoryTheory.Functor.mapDerivedCategoryCompIso_hom_app_factors F G K]
  erw [Category.assoc, Iso.hom_inv_id_app_assoc]
  exact Category.assoc _ _ _

private theorem single_factors (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (X : A) :
    (F.mapDerivedCategorySingleFunctor 0).hom.app X =
      F.mapDerivedCategoryFactors.hom.app
        ((HomologicalComplex.single A (.up ℤ) 0).obj X) ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app X) := by
  erw [← F.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app X]
  erw [Iso.hom_inv_id_app_assoc]

private theorem square_single (e : F ⋙ G ≅ H ⋙ I) (X : A) :
    (CategoryTheory.Functor.mapDerivedCategorySquareIso e).hom.app
        ((DerivedCategory.singleFunctor A 0).obj X) ≫
      I.mapDerivedCategory.map ((H.mapDerivedCategorySingleFunctor 0).hom.app X) ≫
      (I.mapDerivedCategorySingleFunctor 0).hom.app (H.obj X) =
    G.mapDerivedCategory.map ((F.mapDerivedCategorySingleFunctor 0).hom.app X) ≫
      (G.mapDerivedCategorySingleFunctor 0).hom.app (F.obj X) ≫
      (DerivedCategory.singleFunctor D 0).map (e.hom.app X) := by
  let K := (HomologicalComplex.single A (.up ℤ) 0).obj X
  let cF := HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0
  let cG := HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0
  let cH := HomologicalComplex.singleMapHomologicalComplex H (.up ℤ) 0
  let cI := HomologicalComplex.singleMapHomologicalComplex I (.up ℤ) 0
  let ec := NatIso.mapHomologicalComplex e (.up ℤ)
  have hc : ec.hom.app K ≫ (I.mapHomologicalComplex (.up ℤ)).map (cH.hom.app X) ≫
      cI.hom.app (H.obj X) =
      (G.mapHomologicalComplex (.up ℤ)).map (cF.hom.app X) ≫ cG.hom.app (F.obj X) ≫
        (HomologicalComplex.single D (.up ℤ) 0).map (e.hom.app X) := by
    apply HomologicalComplex.Hom.ext
    funext i
    by_cases hi : i = 0
    · subst i
      simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
        ec, NatIso.mapHomologicalComplex, NatTrans.mapHomologicalComplex_app_f,
        HomologicalComplex.single_map_f_self, cF, cG, cH, cI,
        HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
        CategoryTheory.Functor.map_comp, Category.assoc]
      simp only [← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id,
        CategoryTheory.Functor.map_id, Category.id_comp,
        Iso.inv_hom_id_assoc]
      simpa only [K, CategoryTheory.Functor.comp_map, Category.assoc] using!
        congrArg (fun z ↦ z ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 ((H ⋙ I).obj X)).inv)
          (e.hom.naturality (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).hom).symm
    · exact ((F ⋙ G).map_isZero
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 X i hi)).eq_of_src _ _
  rw [single_factors H X, single_factors I (H.obj X), single_factors F X,
    single_factors G (F.obj X)]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  erw [I.mapDerivedCategoryFactors.hom.naturality_assoc (cH.hom.app X)]
  erw [reassoc_of% (square_factors F G H I e K)]
  erw [G.mapDerivedCategoryFactors.hom.naturality_assoc (cF.hom.app X)]
  congr 2
  change DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map _ ≫
      DerivedCategory.Q.map _ = DerivedCategory.Q.map _ ≫
      DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map _
  simp only [← CategoryTheory.Functor.map_comp]
  exact DerivedCategory.Q.congr_map hc
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
section
variable {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  [HasShift A ℤ] [HasShift B ℤ] [HasShift A' ℤ] [HasShift B' ℤ]
  (R : B ⥤ A) (F : A ⥤ A') (G : B ⥤ B') (R' : B' ⥤ A')
  [R.CommShift ℤ] [F.CommShift ℤ] [G.CommShift ℤ] [R'.CommShift ℤ]
  (ρ : R ⋙ F ≅ G ⋙ R') [NatTrans.CommShift ρ.hom ℤ]
private theorem shifted_square (Y : B) (s : ℤ) :
    F.map ((R.commShiftIso s).inv.app Y) ≫ ρ.hom.app (Y⟦s⟧) ≫
      R'.map ((G.commShiftIso s).hom.app Y) ≫ (R'.commShiftIso s).hom.app (G.obj Y) =
    (F.commShiftIso s).hom.app (R.obj Y) ≫ (ρ.hom.app Y)⟦s⟧' := by
  have h := ρ.hom.shift_app_comm s Y
  simp only [Functor.commShiftIso_comp_hom_app] at h
  apply (cancel_epi (F.map ((R.commShiftIso s).hom.app Y))).1
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  simpa only [Category.assoc] using h.symm
end

section
variable {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  [Abelian A] [Abelian B] [Abelian A'] [Abelian B']
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory A'] [HasDerivedCategory B']
  (R : B ⥤ A) (F : A ⥤ A') (G : B ⥤ B') (R' : B' ⥤ A')
  [R.Additive] [F.Additive] [G.Additive] [R'.Additive]
  [Limits.PreservesFiniteLimits R] [Limits.PreservesFiniteColimits R]
  [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
  [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]
  [Limits.PreservesFiniteLimits R'] [Limits.PreservesFiniteColimits R']
  (ρ : R ⋙ F ≅ G ⋙ R')

private theorem shifted_single_square (Y : B) (s : ℤ) :
    F.mapDerivedCategory.map
        (((R.mapDerivedCategorySingleFunctor 0).inv.app Y)⟦s⟧' ≫
          (R.mapDerivedCategory.commShiftIso s).inv.app
            ((DerivedCategory.singleFunctor B 0).obj Y)) ≫
      (CategoryTheory.Functor.mapDerivedCategorySquareIso ρ).hom.app
        (((DerivedCategory.singleFunctor B 0).obj Y)⟦s⟧) ≫
      R'.mapDerivedCategory.map
        ((G.mapDerivedCategory.commShiftIso s).hom.app
            ((DerivedCategory.singleFunctor B 0).obj Y) ≫
          ((G.mapDerivedCategorySingleFunctor 0).hom.app Y)⟦s⟧') ≫
      (R'.mapDerivedCategory.commShiftIso s).hom.app
        ((DerivedCategory.singleFunctor B' 0).obj (G.obj Y)) ≫
      ((R'.mapDerivedCategorySingleFunctor 0).hom.app (G.obj Y))⟦s⟧' =
    (F.mapDerivedCategory.commShiftIso s).hom.app
        ((DerivedCategory.singleFunctor A 0).obj (R.obj Y)) ≫
      ((F.mapDerivedCategorySingleFunctor 0).hom.app (R.obj Y) ≫
        (DerivedCategory.singleFunctor A' 0).map (ρ.hom.app Y))⟦s⟧' := by
  let ρd := CategoryTheory.Functor.mapDerivedCategorySquareIso ρ
  have : NatTrans.CommShift ρd.hom ℤ := by
    dsimp only [ρd, CategoryTheory.Functor.mapDerivedCategorySquareIso,
      Iso.trans_hom, Iso.symm_hom]
    infer_instance
  have h : F.mapDerivedCategory.map ((R.mapDerivedCategorySingleFunctor 0).inv.app Y) ≫
      ρd.hom.app ((DerivedCategory.singleFunctor B 0).obj Y) ≫
      R'.mapDerivedCategory.map ((G.mapDerivedCategorySingleFunctor 0).hom.app Y) ≫
      (R'.mapDerivedCategorySingleFunctor 0).hom.app (G.obj Y) =
      (F.mapDerivedCategorySingleFunctor 0).hom.app (R.obj Y) ≫
        (DerivedCategory.singleFunctor A' 0).map (ρ.hom.app Y) := by
    erw [square_single R F G R' ρ Y]
    rw [← F.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app,
      F.mapDerivedCategory.map_id]
    erw [Category.id_comp]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  erw [R'.mapDerivedCategory.commShiftIso_hom_naturality_assoc
    ((G.mapDerivedCategorySingleFunctor 0).hom.app Y) s]
  erw [reassoc_of% (shifted_square R.mapDerivedCategory F.mapDerivedCategory
    G.mapDerivedCategory R'.mapDerivedCategory ρd
      ((DerivedCategory.singleFunctor B 0).obj Y) s)]
  erw [F.mapDerivedCategory.commShiftIso_hom_naturality_assoc
    ((R.mapDerivedCategorySingleFunctor 0).inv.app Y) s]
  simp only [← (shiftFunctor (DerivedCategory A') s).map_comp]
  rw [h]
  rfl
end

section
variable {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  [Abelian A] [Abelian B] [Abelian A'] [Abelian B']
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory A'] [HasDerivedCategory B']
  (R : B ⥤ A) (F : A ⥤ A') (G : B ⥤ B') (R' : B' ⥤ A')
  [R.Additive] [F.Additive] [G.Additive] [R'.Additive]
  [Limits.PreservesFiniteLimits R] [Limits.PreservesFiniteColimits R]
  [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
  [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]
  [Limits.PreservesFiniteLimits R'] [Limits.PreservesFiniteColimits R']
  (ρ : R ⋙ F ≅ G ⋙ R')

end

section
variable {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  [Abelian A] [Abelian B] [Abelian A'] [Abelian B']
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory A'] [HasDerivedCategory B']
  (R : B ⥤ A) (F : A ⥤ A') (G : B ⥤ B') (R' : B' ⥤ A')
  [R.Additive] [F.Additive] [G.Additive] [R'.Additive]
  [Limits.PreservesFiniteLimits R] [Limits.PreservesFiniteColimits R]
  [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
  [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]
  [Limits.PreservesFiniteLimits R'] [Limits.PreservesFiniteColimits R']
  (ρ : R ⋙ F ≅ G ⋙ R')
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
section
variable {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  {L : A ⥤ B} {R : B ⥤ A} {L' : A' ⥤ B'} {R' : B' ⥤ A'}
  (a : L ⊣ R) (a' : L' ⊣ R') (F : A ⥤ A') (G : B ⥤ B')
  (ρ : R ⋙ F ≅ G ⋙ R') (θ : L ⋙ G ≅ F ⋙ L')
  (hθ : ∀ X, a'.unit.app (F.obj X) ≫ R'.map (θ.inv.app X) =
    F.map (a.unit.app X) ≫ ρ.hom.app (L.obj X))
include hθ in
private theorem normalized_exchange
    (X : A) (X' : A') (Y : B) (Y' : B') (d : F.obj X ⟶ X') (g : G.obj Y ⟶ Y')
    (i : L.obj X ⟶ Y) (i' : L'.obj X' ⟶ Y')
    (f : X ⟶ R.obj Y) (f' : X' ⟶ R'.obj Y')
    (hi : a.unit.app X ≫ R.map i = f) (hi' : a'.unit.app X' ≫ R'.map i' = f')
    (hf : F.map f ≫ ρ.hom.app Y ≫ R'.map g = d ≫ f') :
    G.map i ≫ g = θ.hom.app X ≫ L'.map d ≫ i' := by
  apply (cancel_epi (θ.inv.app X)).1
  simp only [Iso.inv_hom_id_app_assoc]
  apply (a'.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [← Category.assoc, hθ]
  simp only [Category.assoc]
  rw [← reassoc_of% (ρ.hom.naturality i)]
  rw [← F.map_comp_assoc, hi]
  rw [hf]
  rw [← reassoc_of% (a'.unit.naturality d), hi']
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
section
variable {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  [HasShift A ℤ] [HasShift B ℤ] [HasShift A' ℤ] [HasShift B' ℤ]
  (L : A ⥤ B) (L' : A' ⥤ B') (F : A ⥤ A') (G : B ⥤ B')
  [L.CommShift ℤ] [L'.CommShift ℤ] [F.CommShift ℤ] [G.CommShift ℤ]
  (θ : L ⋙ G ≅ F ⋙ L') [NatTrans.CommShift θ.hom ℤ]
  {X₁ X₃ : A} {X₁' X₃' : A'} {H Q : B} {H' Q' : B'}
  (t₁ : F.obj X₁ ⟶ X₁') (t₃ : F.obj X₃ ⟶ X₃')
  (sH : G.obj H ⟶ H') (sQ : G.obj Q ⟶ Q')
  (δ : ShiftedHom X₃ X₁ (1 : ℤ)) (δ' : ShiftedHom X₃' X₁' (1 : ℤ))
  (aF : L.obj X₃ ≅ Q) (aF' : L'.obj X₃' ≅ Q')
  (aB : ShiftedHom (L.obj X₁) H (1 : ℤ))
  (aB' : ShiftedHom (L'.obj X₁') H' (1 : ℤ))
  (hF : G.map aF.hom ≫ sQ = θ.hom.app X₃ ≫ L'.map t₃ ≫ aF'.hom)
  (hB : aB.map G ≫ sH⟦(1 : ℤ)⟧' = θ.hom.app X₁ ≫ L'.map t₁ ≫ aB')
  (hδ : δ.map F ≫ t₁⟦(1 : ℤ)⟧' = t₃ ≫ δ')
end

section NormalizedBoundaries
variable {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  [Abelian A] [Abelian B] [Abelian A'] [Abelian B']
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory A'] [HasDerivedCategory B']
  (R : B ⥤ A) (F : A ⥤ A') (G : B ⥤ B') (R' : B' ⥤ A')
  [R.Additive] [F.Additive] [G.Additive] [R'.Additive]
  [Limits.PreservesFiniteLimits R] [Limits.PreservesFiniteColimits R]
  [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
  [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]
  [Limits.PreservesFiniteLimits R'] [Limits.PreservesFiniteColimits R']
  (ρ : R ⋙ F ≅ G ⋙ R')
  (L : DerivedCategory A ⥤ DerivedCategory B)
  (L' : DerivedCategory A' ⥤ DerivedCategory B') [L.CommShift ℤ] [L'.CommShift ℤ]
  (ad : L ⊣ R.mapDerivedCategory) (ad' : L' ⊣ R'.mapDerivedCategory)
  (θ : L ⋙ G.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ L')
  [NatTrans.CommShift θ.hom ℤ]
  (hθ : ∀ X, ad'.unit.app (F.mapDerivedCategory.obj X) ≫
    R'.mapDerivedCategory.map (θ.inv.app X) =
    F.mapDerivedCategory.map (ad.unit.app X) ≫
      (CategoryTheory.Functor.mapDerivedCategorySquareIso ρ).hom.app (L.obj X))
  (n : ℕ) (S : ShortComplex A) (S' : ShortComplex A')
  (hS : S.ShortExact) (hS' : S'.ShortExact)
  (H Q : B) (H' Q' : B') (i : R.obj H ⟶ S.X₁) (i' : R'.obj H' ⟶ S'.X₁)
  (wi : i ≫ (n • 𝟙 S.X₁) = 0) (wi' : i' ≫ (n • 𝟙 S'.X₁) = 0)
  (hK : (ShortComplex.mk i (n • 𝟙 S.X₁) wi).ShortExact)
  (hK' : (ShortComplex.mk i' (n • 𝟙 S'.X₁) wi').ShortExact)
  (p : S.X₃ ⟶ R.obj Q) (p' : S'.X₃ ⟶ R'.obj Q')
  (aF : L.obj ((DerivedCategory.singleFunctor A 0).obj S.X₃) ≅
    (DerivedCategory.singleFunctor B 0).obj Q)
  (aF' : L'.obj ((DerivedCategory.singleFunctor A' 0).obj S'.X₃) ≅
    (DerivedCategory.singleFunctor B' 0).obj Q')
  (aB : L.obj ((DerivedCategory.singleFunctor A 0).obj S.X₁) ≅
    ((DerivedCategory.singleFunctor B 0).obj H)⟦(1 : ℤ)⟧)
  (aB' : L'.obj ((DerivedCategory.singleFunctor A' 0).obj S'.X₁) ≅
    ((DerivedCategory.singleFunctor B' 0).obj H')⟦(1 : ℤ)⟧)
  (huF : ad.unit.app ((DerivedCategory.singleFunctor A 0).obj S.X₃) ≫
    R.mapDerivedCategory.map aF.hom ≫ (R.mapDerivedCategorySingleFunctor 0).hom.app Q =
    (DerivedCategory.singleFunctor A 0).map p)
  (huF' : ad'.unit.app ((DerivedCategory.singleFunctor A' 0).obj S'.X₃) ≫
    R'.mapDerivedCategory.map aF'.hom ≫ (R'.mapDerivedCategorySingleFunctor 0).hom.app Q' =
    (DerivedCategory.singleFunctor A' 0).map p')
  (huB : ad.unit.app ((DerivedCategory.singleFunctor A 0).obj S.X₁) ≫
    R.mapDerivedCategory.map aB.hom =
      hK.singleδ ≫ ((R.mapDerivedCategorySingleFunctor 0).inv.app H)⟦(1 : ℤ)⟧' ≫
      (R.mapDerivedCategory.commShiftIso (1 : ℤ)).inv.app
        ((DerivedCategory.singleFunctor B 0).obj H))
  (huB' : ad'.unit.app ((DerivedCategory.singleFunctor A' 0).obj S'.X₁) ≫
    R'.mapDerivedCategory.map aB'.hom =
      hK'.singleδ ≫ ((R'.mapDerivedCategorySingleFunctor 0).inv.app H')⟦(1 : ℤ)⟧' ≫
      (R'.mapDerivedCategory.commShiftIso (1 : ℤ)).inv.app
        ((DerivedCategory.singleFunctor B' 0).obj H'))
  (f : S' ≅ F.mapShortComplex.obj S) (h : H' ≅ G.obj H) (q : Q' ≅ G.obj Q)
  (hi : i' ≫ f.hom.τ₁ = R'.map h.hom ≫ ρ.inv.app H ≫ F.map i)
  (hp : f.hom.τ₃ ≫ F.map p = p' ≫ R'.map q.hom ≫ ρ.inv.app Q)

end NormalizedBoundaries

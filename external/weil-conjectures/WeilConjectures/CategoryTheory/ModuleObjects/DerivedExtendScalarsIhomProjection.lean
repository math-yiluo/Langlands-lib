/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidal
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMorphismComp
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsTriangleUnit
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsFlat

/-!
# The projection formula for the derived extension of scalars

Let `φ : R ⟶ S` be a morphism of commutative algebra objects of a closed symmetric monoidal
Grothendieck abelian category `C` with functorial flat resolutions. The derived extension of
scalars `S ⊗ᴸ_R - : D(Mod_R(C)) ⥤ D(Mod_S(C))`, monoidal through
`Functor.leftDerivedFunctorMonoidal`, is left adjoint to the restriction of scalars `D(Res)`
(`Mod.derivedExtendMapDerivedCategoryAdjunction`). This file proves the **projection formula**:
the projection morphism
```
D(Res) N ⊗ᴸ K ⟶ D(Res) (N ⊗ᴸ (S ⊗ᴸ_R K))
```
of this adjunction (`CategoryTheory.Adjunction.projectionMorphism`) is an isomorphism, for all
`N ∈ D(Mod_S(C))` and `K ∈ D(Mod_R(C))`
(`Mod.isIso_derivedExtendMapDerivedCategoryAdjunction_projectionMorphism`).

On the image of complexes `Z` and `P`, the projection morphism is computed, modulo the counits of
the left derived functors and the comparisons for the exact restriction of scalars, by the
projection morphism of the adjunction induced on homotopy categories
(`Mod.derivedProjectionMorphism_Qh_obj`): this only uses the characterizing properties of the unit,
of the counit (`Mod.derivedExtendMapDerivedCategoryAdjunction_counit_app_comp`) and of the tensor
comparison of the derived extension of scalars. On complexes, the projection morphism is, on the
summand `Z^p ⊗ P^q` of the tensor product, the underived projection formula
`Z^p ⊗_R P^q ≅ Z^p ⊗_S (S ⊗_R P^q)` (`Mod.projectionIso`), hence an isomorphism. When `P` is
K-flat and `S ⊗_R P` is K-flat, all the comparison maps are isomorphisms.
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Limits

namespace CategoryTheory.Limits

/-- A morphism between the points of two colimit cofans which is induced by isomorphisms on the
summands is an isomorphism. -/
lemma isIso_of_isColimit_cofan {D : Type*} [Category* D] {J : Type*}
    {A B : J → D} {X Y : D} {i : ∀ j, A j ⟶ X} {i' : ∀ j, B j ⟶ Y}
    (hX : IsColimit (Cofan.mk X i)) (hY : IsColimit (Cofan.mk Y i')) (m : X ⟶ Y)
    (g : ∀ j, A j ⟶ B j) [∀ j, IsIso (g j)] (h : ∀ j, i j ≫ m = g j ≫ i' j) : IsIso m := by
  have hf (j : J) : i' j ≫ Cofan.IsColimit.desc hY (fun j ↦ inv (g j) ≫ i j) = inv (g j) ≫ i j :=
    Cofan.IsColimit.fac hY _ j
  refine ⟨Cofan.IsColimit.desc hY (fun j ↦ inv (g j) ≫ i j), ?_, ?_⟩
  · refine Cofan.IsColimit.hom_ext hX _ _ fun j ↦ ?_
    erw [Category.comp_id, reassoc_of% (h j)]
    rw [hf, IsIso.hom_inv_id_assoc]
    rfl
  · refine Cofan.IsColimit.hom_ext hY _ _ fun j ↦ ?_
    erw [Category.comp_id, reassoc_of% (hf j)]
    rw [h, IsIso.inv_hom_id_assoc]
    rfl

end CategoryTheory.Limits

namespace CategoryTheory.Adjunction

/-- The invertibility of a projection morphism only depends on its second argument up to
isomorphism. -/
lemma isIso_projectionMorphism_iff_of_iso_right {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D] {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G)
    [F.OplaxMonoidal] (A : C) {B B' : D} (e : B ≅ B') :
    IsIso (adj.projectionMorphism A B) ↔ IsIso (adj.projectionMorphism A B') := by
  have h := adj.projectionMorphism_natural_right A e.hom
  constructor
  · intro
    rw [← isIso_comp_left_iff (G.obj A ◁ e.hom), h]
    infer_instance
  · intro
    rw [← isIso_comp_right_iff _ (G.map (A ◁ F.map e.hom)), ← h]
    infer_instance

end CategoryTheory.Adjunction

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v + 1} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [IsGrothendieckAbelian.{v + 1} C]
  [Abelian.HasFunctorialFlatResolution C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S] (φ : R ⟶ S) [IsMonHom φ]

/-- The counit of the derived adjunction `S ⊗ᴸ_R - ⊣ D(comap φ)` on the image of a complex `Z` of
`S`-modules, precomposed with the comparison for the exact restriction of scalars, is the counit
of the derived extension of scalars followed by the levelwise counit `S ⊗_R Z ⟶ Z`. -/
lemma derivedExtendMapDerivedCategoryAdjunction_counit_app_comp
    (Z : HomotopyCategory (Mod C S) (ComplexShape.up ℤ)) :
    (extendScalars φ).leftDerivedFunctor.map ((comap φ).mapDerivedCategoryFactorsh.inv.app Z) ≫
        (derivedExtendMapDerivedCategoryAdjunction φ).counit.app (DerivedCategory.Qh.obj Z) =
      (extendScalars φ).leftDerivedFunctorCounit.app
          (((comap φ).mapHomotopyCategory (ComplexShape.up ℤ)).obj Z) ≫
        DerivedCategory.Qh.map
          (((extendRestrictAdjunction φ).mapHomotopyCategory (ComplexShape.up ℤ)).counit.app
            Z) := by
  have h₁ := (extendRestrictAdjunction φ).mapHomotopyCategory (ComplexShape.up ℤ)
    |>.derivedε_fac_app
    (HomotopyCategory.quasiIso (Mod C S) (ComplexShape.up ℤ))
    (extendScalars φ).leftDerivedFunctorCounit (comap φ).rightDerivedFunctorUnit Z
  have h₃ := NatTrans.congr_app (comap φ).rightDerivedFunctorIsoMapDerivedCategory_hom_fac Z
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h₃
  have h₄ : (comap φ).mapDerivedCategoryFactorsh.inv.app Z ≫
      (comap φ).rightDerivedFunctorIsoMapDerivedCategory.inv.app (DerivedCategory.Qh.obj Z) =
        (comap φ).rightDerivedFunctorUnit.app Z := by
    rw [← h₃, Category.assoc, Iso.hom_inv_id_app]
    exact Category.comp_id _
  simp only [derivedExtendMapDerivedCategoryAdjunction, derivedExtendRestrictAdjunction,
    rightDerivedComapIsoMapDerivedCategory, Adjunction.derivedAdjunction,
    Adjunction.ofNatIsoRight_counit, NatTrans.comp_app, Functor.whiskerRight_app,
    Adjunction.derived_counit]
  rw [← Functor.map_comp_assoc, h₄]
  exact h₁

omit [MonoidalPreadditive C] [Abelian.HasFunctorialFlatResolution C] in
/-- The projection morphism of extension and restriction of scalars is the projection formula
map `Q ⊗_R N ⟶ Q ⊗_S (S ⊗_R N)`, an isomorphism. -/
lemma extendRestrictAdjunction_projectionMorphism (Q : Mod C S) (N : Mod C R) :
    letI := extendScalarsMonoidal φ
    (extendRestrictAdjunction φ).projectionMorphism Q N = projectionHom φ Q N := by
  let := comapLaxMonoidal φ
  let := extendScalarsMonoidal φ
  rw [Adjunction.projectionMorphism]
  erw [Adjunction.leftAdjointOplaxMonoidal_δ]
  rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply, Category.assoc,
    ← Functor.LaxMonoidal.μ_natural_left, tensorHom_def', Category.assoc]
  erw [← comp_whiskerRight_assoc]
  rw [Adjunction.right_triangle_components, id_whiskerRight, Category.id_comp, projectionHom,
    extendRestrictAdjunction_unit_app]
  rfl

omit [Abelian.HasFunctorialFlatResolution C] in
/-- The projection morphism of the adjunction induced on complexes, on the summand
`Z^p ⊗ P^q`, is the projection formula map in degrees `(p, q)`. -/
lemma ιTensorObj_mapHomologicalComplex_projectionMorphism_f (Z : CochainComplex (Mod C S) ℤ)
    (P : CochainComplex (Mod C R) ℤ) (p q n : ℤ) (h : p + q = n) :
    letI := extendScalarsMonoidal φ
    HomologicalComplex.ιTensorObj (((comap φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj Z)
        P p q n h ≫
      (((extendRestrictAdjunction φ).mapHomologicalComplex
        (ComplexShape.up ℤ)).projectionMorphism Z P).f n =
    projectionHom φ (Z.X p) (P.X q) ≫ (comap φ).map (HomologicalComplex.ιTensorObj Z
      (((extendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) p q n h) := by
  let := extendScalarsMonoidal φ
  have hu := (extendRestrictAdjunction φ).unit.naturality
    (HomologicalComplex.ιTensorObj (((comap φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj Z)
      P p q n h)
  have hδ := HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX
    (Functor.OplaxMonoidal.δNatTrans (extendScalars φ)) (ComplexShape.up ℤ)
    (((comap φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj Z) P p q n h
  have hw := CochainComplex.Monoidal.ι_whiskerRight
    (L := ((extendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
    (((extendRestrictAdjunction φ).mapHomologicalComplex (ComplexShape.up ℤ)).counit.app Z) p q n h
  rw [← extendRestrictAdjunction_projectionMorphism, Adjunction.projectionMorphism,
    Adjunction.projectionMorphism, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f, HomologicalComplex.comp_f,
    Functor.map_comp]
  erw [reassoc_of% hu]
  simp only [Category.assoc, ← Functor.map_comp]
  congr 2
  erw [reassoc_of% hδ, hw]
  rfl

omit [Abelian.HasFunctorialFlatResolution C] in
/-- The projection morphism of the adjunction induced on complexes by extension and restriction
of scalars is an isomorphism. -/
lemma isIso_mapHomologicalComplex_projectionMorphism (Z : CochainComplex (Mod C S) ℤ)
    (P : CochainComplex (Mod C R) ℤ) :
    letI := extendScalarsMonoidal φ
    IsIso (((extendRestrictAdjunction φ).mapHomologicalComplex
        (ComplexShape.up ℤ)).projectionMorphism Z P) := by
  let := extendScalarsMonoidal φ
  have (n : ℤ) : IsIso ((((extendRestrictAdjunction φ).mapHomologicalComplex
      (ComplexShape.up ℤ)).projectionMorphism Z P).f n) :=
    isIso_of_isColimit_cofan
    (HomologicalComplex.mapBifunctor.isColimitMapCofan (G := 𝟭 _) _ _ n)
    (HomologicalComplex.mapBifunctor.isColimitMapCofan (G := comap φ) _ _ n) _
    (fun x ↦ projectionHom φ (Z.X x.1.1) (P.X x.1.2))
      (fun x ↦ ιTensorObj_mapHomologicalComplex_projectionMorphism_f φ Z P _ _ n x.2)
  exact HomologicalComplex.Hom.isIso_of_components _

omit [Abelian.HasFunctorialFlatResolution C] in
/-- The projection morphism of the adjunction induced on homotopy categories, on the image of
complexes, is the image of the projection morphism of the adjunction induced on complexes. -/
lemma mapHomotopyCategory_projectionMorphism_quotient (Z : CochainComplex (Mod C S) ℤ)
    (P : CochainComplex (Mod C R) ℤ) :
    letI := extendScalarsMonoidal φ
    ((extendRestrictAdjunction φ).mapHomotopyCategory (ComplexShape.up ℤ)).projectionMorphism
        ((HomotopyCategory.quotient _ _).obj Z) ((HomotopyCategory.quotient _ _).obj P) =
      (HomotopyCategory.quotient _ _).map (((extendRestrictAdjunction φ).mapHomologicalComplex
        (ComplexShape.up ℤ)).projectionMorphism Z P) := by
  let := extendScalarsMonoidal φ
  rw [Adjunction.projectionMorphism, Adjunction.projectionMorphism, Adjunction.homEquiv_unit,
    Adjunction.homEquiv_unit, Functor.map_comp]
  erw [Adjunction.mapHomotopyCategory_unit_app_quotient]
  erw [Adjunction.mapHomotopyCategory_counit_app_quotient]
  rfl

open Functor.LaxMonoidal Functor.OplaxMonoidal in
/-- The projection morphism of `S ⊗ᴸ_R - ⊣ D(comap φ)` on images of objects of the homotopy
categories is the image of the projection morphism of the adjunction induced on the homotopy
categories, modulo the comparison maps. -/
lemma derivedProjectionMorphism_Qh_obj (Z : HomotopyCategory (Mod C S) (ComplexShape.up ℤ))
    (P : HomotopyCategory (Mod C R) (ComplexShape.up ℤ)) :
    letI := extendScalarsMonoidal φ
    letI := (extendScalars φ).leftDerivedFunctorMonoidal
    ((comap φ).mapDerivedCategoryFactorsh.inv.app Z ▷ DerivedCategory.Qh.obj P) ≫
      (derivedExtendMapDerivedCategoryAdjunction φ).projectionMorphism
        (DerivedCategory.Qh.obj Z) (DerivedCategory.Qh.obj P) ≫
      (comap φ).mapDerivedCategory.map (DerivedCategory.Qh.obj Z ◁
        (extendScalars φ).leftDerivedFunctorCounit.app P ≫
        μ DerivedCategory.Qh Z
          (((extendScalars φ).mapHomotopyCategory (ComplexShape.up ℤ)).obj P)) ≫
      (comap φ).mapDerivedCategoryFactorsh.hom.app
        (Z ⊗ ((extendScalars φ).mapHomotopyCategory (ComplexShape.up ℤ)).obj P) =
    μ DerivedCategory.Qh (((comap φ).mapHomotopyCategory (ComplexShape.up ℤ)).obj Z) P ≫
      DerivedCategory.Qh.map
        (((extendRestrictAdjunction φ).mapHomotopyCategory (ComplexShape.up ℤ)).projectionMorphism
          Z P) := by
  let := extendScalarsMonoidal φ
  let := (extendScalars φ).leftDerivedFunctorMonoidal
  have hinner : (extendScalars φ).leftDerivedFunctor.map
      ((comap φ).mapDerivedCategoryFactorsh.inv.app Z ▷ DerivedCategory.Qh.obj P) ≫
      δ (extendScalars φ).leftDerivedFunctor _ _ ≫
      (derivedExtendMapDerivedCategoryAdjunction φ).counit.app (DerivedCategory.Qh.obj Z) ▷ _ ≫
      DerivedCategory.Qh.obj Z ◁ (extendScalars φ).leftDerivedFunctorCounit.app P ≫
      μ DerivedCategory.Qh Z (((extendScalars φ).mapHomotopyCategory (ComplexShape.up ℤ)).obj P) =
    (extendScalars φ).leftDerivedFunctor.map
      (μ DerivedCategory.Qh (((comap φ).mapHomotopyCategory (ComplexShape.up ℤ)).obj Z) P) ≫
      (extendScalars φ).leftDerivedFunctorCounit.app _ ≫
      DerivedCategory.Qh.map (δ ((extendScalars φ).mapHomotopyCategory (ComplexShape.up ℤ)) _ P ≫
        ((extendRestrictAdjunction φ).mapHomotopyCategory (ComplexShape.up ℤ)).counit.app Z ▷
          _) := by
    have h4 := (extendScalars φ).leftDerivedTensorComparison_app_app_comp_tensorHom
      (((comap φ).mapHomotopyCategory (ComplexShape.up ℤ)).obj Z) P
    rw [← δ_natural_left_assoc, ← comp_whiskerRight_assoc,
      derivedExtendMapDerivedCategoryAdjunction_counit_app_comp, comp_whiskerRight_assoc]
    erw [← whisker_exchange_assoc]
    erw [μ_natural_left]
    rw [← tensorHom_def_assoc]
    erw [reassoc_of% h4]
    rw [Functor.map_comp]
    rfl
  have hη := (derivedExtendMapDerivedCategoryAdjunction φ).unit.naturality
    ((comap φ).mapDerivedCategoryFactorsh.inv.app Z ▷ DerivedCategory.Qh.obj P)
  have hη' := (derivedExtendMapDerivedCategoryAdjunction φ).unit.naturality
    (μ DerivedCategory.Qh (((comap φ).mapHomotopyCategory (ComplexShape.up ℤ)).obj Z) P)
  have hi := (comap φ).mapDerivedCategoryFactorsh.hom.naturality
    (δ ((extendScalars φ).mapHomotopyCategory (ComplexShape.up ℤ)) _ P ≫
        ((extendRestrictAdjunction φ).mapHomotopyCategory (ComplexShape.up ℤ)).counit.app Z ▷ _)
  have hu := derivedExtendMapDerivedCategoryAdjunction_unit_app_fac φ
    (((comap φ).mapHomotopyCategory (ComplexShape.up ℤ)).obj Z ⊗ P)
  dsimp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map] at hη hη' hi
  rw [Adjunction.projectionMorphism, Adjunction.projectionMorphism, Adjunction.homEquiv_unit,
    Adjunction.homEquiv_unit, Category.assoc, reassoc_of% hη, ← Functor.map_comp_assoc,
    ← Functor.map_comp_assoc]
  simp only [Category.assoc]
  erw [hinner]
  rw [Functor.map_comp, Category.assoc, ← reassoc_of% hη', Functor.map_comp,
    Category.assoc, hi, reassoc_of% hu,
    Functor.map_comp, Functor.map_comp]
  simp only [Functor.map_comp]

/-- **The projection formula for the derived extension of scalars**: the projection morphism
`D(Res) N ⊗ᴸ K ⟶ D(Res) (N ⊗ᴸ (S ⊗ᴸ_R K))` of `S ⊗ᴸ_R - ⊣ D(comap φ)` is an isomorphism. -/
theorem isIso_derivedExtendMapDerivedCategoryAdjunction_projectionMorphism
    (N : DerivedCategory (Mod C S)) (K : DerivedCategory (Mod C R)) :
    letI := extendScalarsMonoidal φ
    letI := (extendScalars φ).leftDerivedFunctorMonoidal
    IsIso ((derivedExtendMapDerivedCategoryAdjunction φ).projectionMorphism N K) := by
  let := extendScalarsMonoidal φ
  let := (extendScalars φ).leftDerivedFunctorMonoidal
  have := Localization.essSurj (DerivedCategory.Qh (C := Mod C S))
    (HomotopyCategory.quasiIso (Mod C S) (ComplexShape.up ℤ))
  obtain ⟨P, hP, ⟨e⟩⟩ := (extendScalars φ).exists_kFlatKFlatMap_iso K
  rw [← Adjunction.isIso_projectionMorphism_iff_of_iso_right _ _ e,
    ← Adjunction.isIso_projectionMorphism_iff_of_iso _
      (DerivedCategory.Qh.objObjPreimageIso N)]
  generalize DerivedCategory.Qh.objPreimage N = Z
  obtain ⟨Z', rfl⟩ := HomotopyCategory.quotient_obj_surjective Z
  obtain ⟨P', rfl⟩ := HomotopyCategory.quotient_obj_surjective P
  have h := derivedProjectionMorphism_Qh_obj φ ((HomotopyCategory.quotient _ _).obj Z')
    ((HomotopyCategory.quotient _ _).obj P')
  rw [mapHomotopyCategory_projectionMorphism_quotient] at h
  have := isIso_mapHomologicalComplex_projectionMorphism φ Z' P'
  have := (extendScalars φ).isIso_leftDerivedFunctorCounit_app_of_kFlat' _ hP.1
  have hμ : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Qh
      (((comap φ).mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient _ _).obj Z')) ((HomotopyCategory.quotient _ _).obj P')) :=
    Functor.isIso_μNatTrans_Qh_app_app_of_kFlat _ _ hP.1
  have hμ' : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Qh
      ((HomotopyCategory.quotient _ _).obj Z') (((extendScalars φ).mapHomotopyCategory
        (ComplexShape.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj P'))) :=
    Functor.isIso_μNatTrans_Qh_app_app_of_kFlat _ _ hP.2
  have hb : IsIso ((comap φ).mapDerivedCategory.map
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj Z') ◁
        (extendScalars φ).leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj P') ≫
      Functor.LaxMonoidal.μ DerivedCategory.Qh ((HomotopyCategory.quotient _ _).obj Z')
        (((extendScalars φ).mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient _ _).obj P')))) := by
    have : IsIso (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj Z') ◁
        (extendScalars φ).leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj P')) :=
      inferInstance
    infer_instance
  have hd : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Qh
      (((comap φ).mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient _ _).obj Z')) ((HomotopyCategory.quotient _ _).obj P') ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
        (((extendRestrictAdjunction φ).mapHomologicalComplex (ComplexShape.up ℤ)).projectionMorphism
          Z' P'))) := inferInstance
  rw [← h, isIso_comp_left_iff, isIso_comp_right_iff] at hd
  exact hd

end CategoryTheory.Mod

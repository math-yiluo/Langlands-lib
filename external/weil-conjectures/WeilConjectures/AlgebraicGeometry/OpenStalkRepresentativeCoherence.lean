/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OpenDerivedAdditiveStalkIso
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Representative coherence for exact open stalk restriction

Source: Stacks Project, Tags 0098, 08DW and 015F; exact localization factorization.
(blueprint: lem-pc-open-stalk-representative-coherence).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
open SingleComplexBaseChange

private theorem comp_factors_inv
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (K : CochainComplex C ℤ) :
    G.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app K) ≫
        (Functor.mapDerivedCategoryCompIso F G).hom.app (DerivedCategory.Q.obj K) =
      (F ⋙ G).mapDerivedCategoryFactors.inv.app K := by
  let := comp_preservesFiniteLimits F G
  let := comp_preservesFiniteColimits F G
  have h := Functor.mapDerivedCategoryCompIso_fac F G K
  have hid : (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G))
      (.up ℤ)).hom.app K = 𝟙 _ := by
    ext j
    rfl
  rw [hid] at h
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at h
  rw [← cancel_mono ((F ⋙ G).mapDerivedCategoryFactors.hom.app K)]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [← h, Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app]
  rfl

private theorem comp_factors_hom
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (K : CochainComplex C ℤ) :
    (Functor.mapDerivedCategoryCompIso F G).inv.app (DerivedCategory.Q.obj K) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) =
      (F ⋙ G).mapDerivedCategoryFactors.hom.app K := by
  let := comp_preservesFiniteLimits F G
  let := comp_preservesFiniteColimits F G
  have h := Functor.mapDerivedCategoryCompIso_fac F G K
  have hid : (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G))
      (.up ℤ)).hom.app K = 𝟙 _ := by
    ext j
    rfl
  rw [hid] at h
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at h
  exact h

private theorem homology_inv_app_Q
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (i : ℤ) (K : CochainComplex C ℤ) :
    (F.mapDerivedCategoryHomologyFunctorIso i).inv.app (DerivedCategory.Q.obj K) ≫
        F.map ((DerivedCategory.homologyFunctorFactors C i).hom.app K) =
      (DerivedCategory.homologyFunctor D i).map (F.mapDerivedCategoryFactors.hom.app K) ≫
        (DerivedCategory.homologyFunctorFactors D i).hom.app
          ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
        (F.mapHomologicalComplexHomologyIso (.up ℤ) i).hom.app K := by
  apply (cancel_epi ((F.mapDerivedCategoryHomologyFunctorIso i).hom.app
    (DerivedCategory.Q.obj K))).mp
  rw [Iso.hom_inv_id_app_assoc,
    Functor.mapDerivedCategoryHomologyFunctorIso_hom_app_Q]
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id]
  simp

private theorem complex_homology_iso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] [F.PreservesHomology]
    (i : ℤ) (K : CochainComplex C ℤ) :
    (F.mapHomologicalComplexHomologyIso (.up ℤ) i).app K =
      (K.sc i).mapHomologyIso F := by
  apply Iso.ext
  simp only [Functor.comp_obj, Functor.mapHomologicalComplexHomologyIso,
    Functor.mapHomologicalComplexCompShortComplexFunctorIso, Functor.isoWhiskerRight_refl,
    ShortComplex.homologyFunctorIso, Iso.refl_trans, NatIso.trans_app, Iso.trans_hom, Iso.app_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    HomologicalComplex.homologyFunctorIso_hom_app, Iso.symm_hom,
    Functor.associator_inv_app, Functor.associator_hom_app, NatIso.ofComponents_hom_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    HomologicalComplex.homologyFunctorIso_inv_app, Category.id_comp]
  erw [Category.id_comp, Category.id_comp, CategoryTheory.Functor.map_id, Category.comp_id]

-- Abstract functors keep localization calculations from unfolding the stalk construction.
private theorem representative_factors
    {C D A B E : Type*}
    [Category C] [Category D] [Category A] [Category B] [Category E]
    [Abelian C] [Abelian D] [Abelian A] [Abelian B] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory E]
    (R : C ⥤ D) (L₀ : D ⥤ A) (L : C ⥤ B) (F₀ : A ⥤ E) (F : B ⥤ E)
    [R.Additive] [L₀.Additive] [L.Additive] [F₀.Additive] [F.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits L₀] [PreservesFiniteColimits L₀]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits F₀] [PreservesFiniteColimits F₀]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (γ : R ⋙ L₀ ⋙ F₀ ≅ L ⋙ F)
    (M : CochainComplex D ℤ) (N : CochainComplex C ℤ)
    (a : M ⟶ (R.mapHomologicalComplex (.up ℤ)).obj N) :
      F₀.mapDerivedCategoryFactors.inv.app ((L₀.mapHomologicalComplex (.up ℤ)).obj M) ≫
        F₀.mapDerivedCategory.map
          (L₀.mapDerivedCategoryFactors.inv.app M ≫
            L₀.mapDerivedCategory.map (DerivedCategory.Q.map a) ≫
            L₀.mapDerivedCategory.map (R.mapDerivedCategoryFactors.inv.app N)) ≫
        (Functor.mapDerivedCategoryCompIso L₀ F₀).hom.app
          (R.mapDerivedCategory.obj (DerivedCategory.Q.obj N)) ≫
        (Functor.mapDerivedCategoryCompIso R (L₀ ⋙ F₀)).hom.app
          (DerivedCategory.Q.obj N) ≫
        (Functor.mapDerivedCategoryNatIso γ).hom.app (DerivedCategory.Q.obj N) ≫
        (Functor.mapDerivedCategoryCompIso L F).inv.app (DerivedCategory.Q.obj N) ≫
        F.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app N) ≫
        F.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj N) =
      DerivedCategory.Q.map
        ((F₀.mapHomologicalComplex (.up ℤ)).map
            ((L₀.mapHomologicalComplex (.up ℤ)).map a) ≫
          (NatTrans.mapHomologicalComplex γ.hom (.up ℤ)).app N) := by
  let := comp_preservesFiniteLimits L₀ F₀
  let := comp_preservesFiniteColimits L₀ F₀
  let := comp_preservesFiniteLimits L F
  let := comp_preservesFiniteColimits L F
  let := comp_preservesFiniteLimits R (L₀ ⋙ F₀)
  let := comp_preservesFiniteColimits R (L₀ ⋙ F₀)
  have ha := L₀.mapDerivedCategoryFactors.inv.naturality a
  simp only [Functor.comp_map] at ha
  erw [← reassoc_of% ha, CategoryTheory.Functor.map_comp]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  have hb := F₀.mapDerivedCategoryFactors.inv.naturality
    ((L₀.mapHomologicalComplex (.up ℤ)).map a)
  simp only [Functor.comp_map] at hb
  rw [← reassoc_of% hb]
  have hc := (Functor.mapDerivedCategoryCompIso L₀ F₀).hom.naturality
    (R.mapDerivedCategoryFactors.inv.app N)
  simp only [Functor.comp_map] at hc
  rw [reassoc_of% hc, reassoc_of% (comp_factors_inv L₀ F₀
    ((R.mapHomologicalComplex (.up ℤ)).obj N)),
    reassoc_of% (comp_factors_inv R (L₀ ⋙ F₀) N), comp_factors_hom L F N]
  erw [Functor.mapDerivedCategoryNatIso_fac γ N, Iso.inv_hom_id_app_assoc]

-- Homology of the preceding localization identity, with both forgetful comparisons.
private theorem representative_cohomology
    {C D A B E : Type*}
    [Category C] [Category D] [Category A] [Category B] [Category E]
    [Abelian C] [Abelian D] [Abelian A] [Abelian B] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory E]
    (R : C ⥤ D) (L₀ : D ⥤ A) (L : C ⥤ B) (F₀ : A ⥤ E) (F : B ⥤ E)
    [R.Additive] [L₀.Additive] [L.Additive] [F₀.Additive] [F.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits L₀] [PreservesFiniteColimits L₀]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits F₀] [PreservesFiniteColimits F₀]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (γ : R ⋙ L₀ ⋙ F₀ ≅ L ⋙ F)
    (M : CochainComplex D ℤ) (N : CochainComplex C ℤ)
    (a : M ⟶ (R.mapHomologicalComplex (.up ℤ)).obj N) (i : ℤ) :
    F₀.map ((DerivedCategory.homologyFunctorFactors A i).inv.app
        ((L₀.mapHomologicalComplex (.up ℤ)).obj M)) ≫
      F₀.map ((DerivedCategory.homologyFunctor A i).map
        (L₀.mapDerivedCategoryFactors.inv.app M)) ≫
      F₀.map ((DerivedCategory.homologyFunctor A i).map
        (L₀.mapDerivedCategory.map (DerivedCategory.Q.map a))) ≫
      F₀.map ((DerivedCategory.homologyFunctor A i).map
        (L₀.mapDerivedCategory.map (R.mapDerivedCategoryFactors.inv.app N))) ≫
      (F₀.mapDerivedCategoryHomologyFunctorIso i).hom.app
        (L₀.mapDerivedCategory.obj (R.mapDerivedCategory.obj (DerivedCategory.Q.obj N))) ≫
      (DerivedCategory.homologyFunctor E i).map
        ((Functor.mapDerivedCategoryCompIso L₀ F₀).hom.app
          (R.mapDerivedCategory.obj (DerivedCategory.Q.obj N))) ≫
      (DerivedCategory.homologyFunctor E i).map
        ((Functor.mapDerivedCategoryCompIso R (L₀ ⋙ F₀)).hom.app (DerivedCategory.Q.obj N)) ≫
      (DerivedCategory.homologyFunctor E i).map
        ((Functor.mapDerivedCategoryNatIso γ).hom.app (DerivedCategory.Q.obj N)) ≫
      (DerivedCategory.homologyFunctor E i).map
        ((Functor.mapDerivedCategoryCompIso L F).inv.app (DerivedCategory.Q.obj N)) ≫
      (F.mapDerivedCategoryHomologyFunctorIso i).inv.app
        (L.mapDerivedCategory.obj (DerivedCategory.Q.obj N)) ≫
      F.map ((DerivedCategory.homologyFunctor B i).map
        (L.mapDerivedCategoryFactors.hom.app N)) ≫
      F.map ((DerivedCategory.homologyFunctorFactors B i).hom.app
        ((L.mapHomologicalComplex (.up ℤ)).obj N)) =
    ((((L₀.mapHomologicalComplex (.up ℤ)).obj M).sc i).mapHomologyIso F₀).inv ≫
      HomologicalComplex.homologyMap
        ((F₀.mapHomologicalComplex (.up ℤ)).map
            ((L₀.mapHomologicalComplex (.up ℤ)).map a) ≫
          (NatTrans.mapHomologicalComplex γ.hom (.up ℤ)).app N) i ≫
      ((((L.mapHomologicalComplex (.up ℤ)).obj N).sc i).mapHomologyIso F).hom := by
  let := comp_preservesFiniteLimits L₀ F₀
  let := comp_preservesFiniteColimits L₀ F₀
  let := comp_preservesFiniteLimits L F
  let := comp_preservesFiniteColimits L F
  let := comp_preservesFiniteLimits R (L₀ ⋙ F₀)
  let := comp_preservesFiniteColimits R (L₀ ⋙ F₀)
  have h₁ := (F₀.mapDerivedCategoryHomologyFunctorIso i).hom.naturality
    (L₀.mapDerivedCategory.map (R.mapDerivedCategoryFactors.inv.app N))
  have h₂ := (F₀.mapDerivedCategoryHomologyFunctorIso i).hom.naturality
    (L₀.mapDerivedCategory.map (DerivedCategory.Q.map a))
  have h₃ := (F₀.mapDerivedCategoryHomologyFunctorIso i).hom.naturality
    (L₀.mapDerivedCategoryFactors.inv.app M)
  have h₄ := (F.mapDerivedCategoryHomologyFunctorIso i).inv.naturality
    (L.mapDerivedCategoryFactors.hom.app N)
  simp only [Functor.comp_map] at h₁ h₂ h₃ h₄
  erw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃, reassoc_of% h₄.symm]
  erw [Functor.mapDerivedCategoryHomologyFunctorIso_hom_app_Q]
  erw [homology_inv_app_Q]
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp_assoc]
  erw [Iso.inv_hom_id_app, F₀.map_id, Category.id_comp]
  have hraw := representative_factors R L₀ L F₀ F γ M N a
  erw [hraw]
  let ρ := (F₀.mapHomologicalComplex (.up ℤ)).map
    ((L₀.mapHomologicalComplex (.up ℤ)).map a) ≫
      (NatTrans.mapHomologicalComplex γ.hom (.up ℤ)).app N
  have hn := (DerivedCategory.homologyFunctorFactors E i).hom.naturality ρ
  simp only [Functor.comp_map] at hn
  erw [reassoc_of% hn, Iso.inv_hom_id_app_assoc]
  rw [← Iso.app_inv, ← Iso.app_hom, complex_homology_iso, complex_homology_iso]
  rfl


/-- Exact open stalk comparison on a morphism of representatives.

Proof: first apply comparisonStalkHomologyIso_naturality to a. Expand the
comparison for the restricted representative and openDerivedAdditiveStalkIso.
Apply mapDerivedCategoryCompIso_fac to the composites of restriction, stalk
and forgetting scalars, and mapDerivedCategoryNatIso_fac to the same-germ
comparison gamma. Apply mapDerivedCategoryHomologyFunctorIso_hom_app_Q to
both forgetful functors. The localization factors cancel with their inverses,
leaving homology of the stalk map of a followed by gamma. The naturality of
ShortComplex.mapHomologyIso gives the displayed inverse factor at the source
and direct factor at the target. All equalities are natural-transformation
identities, so zero complexes and zero homology require no extra hypotheses;
for the top open this specializes to the identity restriction comparison.
An empty open has no point z.
Source: Stacks Project, Tags 0098, 08DW and 015F; the exact functor factorization
identities named above.
(blueprint: lem-pc-open-stalk-representative-coherence). -/
theorem openStalk_representative_coherence
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (X : Scheme.{u}) (U : X.Opens) (z : U.toScheme) (i : ℤ)
    (M : CochainComplex (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) ℤ)
    (N : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    letI : (schemeOpenRestriction X U).Additive := schemeOpenRestriction_additive X U
    let R := schemeOpenRestriction X U
    let L₀ := RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace z
    let L := RingedSpace.moduleStalkFunctor X.toRingedSpace z.val
    let F₀ := forget₂ (ModuleCat.{u} (U.toScheme.presheaf.stalk z)) AddCommGrpCat.{u}
    let F := forget₂ (ModuleCat.{u} (X.presheaf.stalk z.val)) AddCommGrpCat.{u}
    let S₀ := (L₀.mapHomologicalComplex (.up ℤ)).obj M
    let S := (L.mapHomologicalComplex (.up ℤ)).obj N
    let γ : R ⋙ L₀ ⋙ F₀ ≅ L ⋙ F :=
      Functor.isoWhiskerRight (Scheme.Modules.overFunctorEquiv U) (L₀ ⋙ F₀) ≪≫
      Scheme.Modules.restrictStalkNatIso U.ι z
    ∀ (a : M ⟶ (R.mapHomologicalComplex (.up ℤ)).obj N),
      let b := DerivedCategory.Q.map a ≫ R.mapDerivedCategoryFactors.inv.app N
      let ρ := (F₀.mapHomologicalComplex (.up ℤ)).map
          ((L₀.mapHomologicalComplex (.up ℤ)).map a) ≫
        (NatTrans.mapHomologicalComplex γ.hom (.up ℤ)).app N
      F₀.map (comparisonStalkHomologyIso U.toScheme z M i).inv ≫
          F₀.map ((comparisonStalkCohomology U.toScheme z i).map b) ≫
          (openDerivedAdditiveStalkIso X U z i).hom.app (DerivedCategory.Q.obj N) =
        ((S₀.sc i).mapHomologyIso F₀).inv ≫ HomologicalComplex.homologyMap ρ i ≫
          ((S.sc i).mapHomologyIso F).hom ≫
          F.map (comparisonStalkHomologyIso X z.val N i).inv := by
  let : (schemeOpenRestriction X U).Additive := schemeOpenRestriction_additive X U
  dsimp only
  intro a
  let := HasDerivedCategory.standard (ModuleCat.{u} (U.toScheme.presheaf.stalk z))
  let := HasDerivedCategory.standard (ModuleCat.{u} (X.presheaf.stalk z.val))
  let := HasDerivedCategory.standard AddCommGrpCat.{u}
  let R := schemeOpenRestriction X U
  let L₀ := RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace z
  let L := RingedSpace.moduleStalkFunctor X.toRingedSpace z.val
  let F₀ := forget₂ (ModuleCat.{u} (U.toScheme.presheaf.stalk z)) AddCommGrpCat.{u}
  let F := forget₂ (ModuleCat.{u} (X.presheaf.stalk z.val)) AddCommGrpCat.{u}
  apply (cancel_mono (F.map (comparisonStalkHomologyIso X z.val N i).hom)).mp
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_map]
  simp only [Category.comp_id]
  simp only [openDerivedAdditiveStalkIso, comparisonStalkCohomology,
    comparisonDerivedStalk, comparisonStalkHomologyIso, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.app_inv, Iso.app_hom, Functor.mapIso_inv, Functor.mapIso_hom,
    CategoryTheory.Functor.map_comp, Functor.comp_map, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc]
  let γ : R ⋙ L₀ ⋙ F₀ ≅ L ⋙ F :=
    Functor.isoWhiskerRight (Scheme.Modules.overFunctorEquiv U) (L₀ ⋙ F₀) ≪≫
      Scheme.Modules.restrictStalkNatIso U.ι z
  exact representative_cohomology R L₀ L F₀ F γ M N a i

end AlgebraicGeometry

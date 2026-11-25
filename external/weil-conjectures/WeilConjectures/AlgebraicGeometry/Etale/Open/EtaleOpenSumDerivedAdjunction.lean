/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMapProjection
public import Mathlib.Algebra.Homology.Localization

import all Mathlib.Algebra.Homology.Localization

/-! # Agreement of open and etale sum adjunctions on derived categories -/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local instance 2000] Abelian.toPreadditive

attribute [local irreducible] lowerStar upperStar
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
  derivedEtaleLowerShriekUpperStarAdjunction
  derivedOpenImmersionLowerShriekUpperStarAdjunction mapDerivedUpperStarLowerStarAdjunction

private lemma exact_factor_hom_quotient
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : CochainComplex C ℤ) :
    F.mapDerivedCategoryFactorsh.hom.app
        ((HomotopyCategory.quotient C (.up ℤ)).obj K) =
      F.mapDerivedCategoryFactors.hom.app K := by
  rw [F.mapDerivedCategoryFactorsh_hom_app]
  simp only [DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv,
    Functor.comp_obj, Quotient.lift.isLift_hom]
  erw [F.mapDerivedCategory.map_id, Category.id_comp, Category.id_comp,
    DerivedCategory.Qh.map_id, Category.comp_id]

/-- The canonical open and etale-sum derived adjunctions agree for an open immersion.
Source: Stacks Project, Etale Cohomology, Tags 03S3 and 03S5; derived.tex Tag 0FND.
(blueprint: lem-pur-etale-open-sum-derived-adjunction).

Proof: an adjunction is determined by its unit. Evaluate the two units on a complex
representative under the derived localization. For the open adjunction, the standard
unit factorization through the homotopy category gives the ordinary degreewise unit
followed by the inverse exact-functor factorizations. The homotopy and cochain exact
factorizations agree on quotient complexes, because both quotient comparison maps
have identity components. The localization unit formula gives exactly the same
composite for the etale sum adjunction. Cancel the invertible exact factorizations,
use quotient-localization naturality, and extend the equality by localization. -/
theorem etaleOpenSumDerivedAdjunction
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j =
      derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j inferInstance := by
  apply Adjunction.ext
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
      (.up ℤ))
  intro K
  let L := openImmersionLowerShriek (ModuleCat.{u + 1} A) j
  let R := upperStar (ModuleCat.{u + 1} A) j
  have h := (openImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) j).mapDerivedCategoryAdjunction_unit_app_fac
      ((HomotopyCategory.quotient _ (.up ℤ)).obj K)
  change (openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) j).mapDerivedCategoryAdjunction.unit.app
        (DerivedCategory.Q.obj K) ≫
      R.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj K)) ≫
      R.mapDerivedCategoryFactorsh.hom.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj
          ((L.mapHomologicalComplex (.up ℤ)).obj K)) = _ at h
  rw [exact_factor_hom_quotient, exact_factor_hom_quotient,
    Adjunction.mapHomotopyCategory_unit_app_quotient] at h
  unfold derivedEtaleLowerShriekUpperStarAdjunction
  rw [Adjunction.localization_unit_app]
  change _ = DerivedCategory.Q.map
      (((openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).unit.app K) ≫
    R.mapDerivedCategoryFactors.inv.app ((L.mapHomologicalComplex (.up ℤ)).obj K) ≫
      R.mapDerivedCategory.map (L.mapDerivedCategoryFactors.inv.app K)
  apply (cancel_mono (R.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app K) ≫
    R.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj K))).1
  simp only [Category.assoc, ← R.mapDerivedCategory.map_comp_assoc,
    Iso.inv_hom_id_app]
  erw [R.mapDerivedCategory.map_id, Category.id_comp, Iso.inv_hom_id_app,
    Category.comp_id]
  have hq := DerivedCategory.quotientCompQhIso_hom_naturality
    (((openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).unit.app K)
  change _ ≫ 𝟙 _ = 𝟙 _ ≫ _ at hq
  simp only [Category.comp_id, Category.id_comp] at hq
  rw [hq] at h
  unfold derivedOpenImmersionLowerShriekUpperStarAdjunction
  exact h

end AlgebraicGeometry.Etale

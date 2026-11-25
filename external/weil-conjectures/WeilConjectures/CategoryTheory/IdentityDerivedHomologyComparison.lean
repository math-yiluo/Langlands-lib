/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Identity functor and the derived homology comparison

Source: the canonical localization constructions in ExactFunctor.lean.
(blueprint: lem-weil-pbc-identity-derived-homology-comparison)
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.Functor

/-- The homology comparison of the identity functor is homology of its inverse
canonical derived identity comparison.

Source: Stacks Project, Tag 01F8, equation 01FA; the localization constructions
`mapDerivedCategoryHomologyFunctorIso` and `mapDerivedCategoryPlusIdIso`.
(blueprint: lem-weil-pbc-identity-derived-homology-comparison)

Proof: on complexes the identity functor acts as identity on kernels, cokernels,
and hence homology. The induced homology comparison is therefore homology of the
canonical comparison of the complex mapped by identity with the original complex.
The localization factorization equations transport this equality to the derived
category: equality of natural transformations can be checked after precomposition
with the localization functor. Restrict the resulting natural-transformation
identity along the fully faithful inclusion of bounded below derived objects.
The bounded below compatibility isomorphisms cancel and give the displayed
formula. All degrees and all bounded below objects are allowed. -/
theorem identityDerivedHomologyComparison {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (n : ℤ) (K : DerivedCategory.Plus C) :
    ((𝟭 C).mapDerivedCategoryPlusHomologyFunctorIso n).hom.app K =
      (DerivedCategory.Plus.homologyFunctor C n).map
        ((mapDerivedCategoryPlusIdIso C).inv.app K) := by
  have core (X : DerivedCategory C) :
      ((𝟭 C).mapDerivedCategoryHomologyFunctorIso n).hom.app X =
        (DerivedCategory.homologyFunctor C n).map
          ((mapDerivedCategoryIdIso C).inv.app X) := by
    have hC (K : CochainComplex C ℤ) :
        ((𝟭 C).mapHomologicalComplexHomologyIso (.up ℤ) n).hom.app K = 𝟙 _ := by
      have hS (S : ShortComplex C) : (S.mapHomologyIso (𝟭 C)).hom = 𝟙 _ := by
        let γ : ShortComplex.LeftHomologyMapData (𝟙 S)
            S.homologyData.left (S.homologyData.left.map (𝟭 C)) :=
          { φK := 𝟙 _
            φH := 𝟙 _ }
        have hg := γ.homologyMap_comm
        simpa [γ, ShortComplex.mapHomologyIso, ShortComplex.LeftHomologyData.homologyIso,
          ShortComplex.leftHomologyIso, ShortComplex.LeftHomologyData.leftHomologyIso,
          ← ShortComplex.leftHomologyMap'_comp] using hg
      dsimp [mapHomologicalComplexHomologyIso, mapHomologicalComplexCompShortComplexFunctorIso,
        ShortComplex.homologyFunctorIso, HomologicalComplex.homologyFunctorIso]
      simp only [Functor.map_id, Category.id_comp, hS]
      erw [Category.id_comp]
      rfl
    have hId (K : CochainComplex C ℤ) :
        (mapDerivedCategoryIdIso C).hom.app (DerivedCategory.Q.obj K) =
          (𝟭 C).mapDerivedCategoryFactors.hom.app K := by
      rw [mapDerivedCategoryIdIso_hom_app]
      have h : (mapHomologicalComplexIdIso C (.up ℤ)).hom.app K = 𝟙 _ := rfl
      rw [h]
      erw [DerivedCategory.Q.map_id, Category.comp_id]
    have hInv (K : CochainComplex C ℤ) :
        (mapDerivedCategoryIdIso C).inv.app (DerivedCategory.Q.obj K) =
          (𝟭 C).mapDerivedCategoryFactors.inv.app K := by
      apply (cancel_mono ((𝟭 C).mapDerivedCategoryFactors.hom.app K)).1
      rw [← hId]
      rw [Iso.inv_hom_id_app]
      rw [hId, Iso.inv_hom_id_app]
      rfl
    have hCInv (K : CochainComplex C ℤ) :
        ((𝟭 C).mapHomologicalComplexHomologyIso (.up ℤ) n).inv.app K = 𝟙 _ := by
      apply (cancel_epi
        (((𝟭 C).mapHomologicalComplexHomologyIso (.up ℤ) n).hom.app K)).1
      rw [Iso.hom_inv_id_app, hC]
      erw [Category.id_comp]
      rfl
    let τ := Functor.whiskerRight (mapDerivedCategoryIdIso C).inv
      (DerivedCategory.homologyFunctor C n)
    have h : ((𝟭 C).mapDerivedCategoryHomologyFunctorIso n).hom = τ := by
      refine Localization.natTrans_ext DerivedCategory.Q
        (HomologicalComplex.quasiIso C (.up ℤ)) (fun K ↦ ?_)
      dsimp only [τ, Functor.whiskerRight_app]
      rw [mapDerivedCategoryHomologyFunctorIso_hom_app_Q, hInv, hCInv]
      erw [Functor.id_map, Category.id_comp, Iso.hom_inv_id_app_assoc]
    exact congr_app h X
  have compatibility :
      (DerivedCategory.homologyFunctor C n).map
          (DerivedCategory.Plus.ι.preimage
            ((mapDerivedCategoryIdIso C).inv.app K.obj ≫
              (𝟭 C).mapDerivedCategoryPlusCompatibility.inv.app K)).hom =
        (DerivedCategory.homologyFunctor C n).map
            ((mapDerivedCategoryIdIso C).inv.app K.obj) ≫
          (DerivedCategory.homologyFunctor C n).map
            ((𝟭 C).mapDerivedCategoryPlusCompatibility.inv.app K) := by
    change (DerivedCategory.homologyFunctor C n).map
      (DerivedCategory.Plus.ι.map (DerivedCategory.Plus.ι.preimage _)) = _
    rw [Functor.map_preimage, Functor.map_comp]
  have h := core (DerivedCategory.Plus.ι.obj K)
  have h' := congrArg (fun f ↦ f ≫
      (DerivedCategory.homologyFunctor C n).map
        ((𝟭 C).mapDerivedCategoryPlusCompatibility.inv.app K)) h
  simpa [mapDerivedCategoryPlusHomologyFunctorIso, mapDerivedCategoryPlusIdIso,
    Functor.map_comp, DerivedCategory.Plus.homologyFunctor,
    DerivedCategory.Plus.ι.map_preimage, Functor.map_preimage, compatibility] using h'


end CategoryTheory.Functor

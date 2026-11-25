/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiber
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModules
public import WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
public import WeilConjectures.AlgebraicGeometry.ProEtaleOperations
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.AlgebraicGeometry.CompactSupportComparisonUnit
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleConstantModuleEncoding
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelLocalConstancy
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelStalks
import WeilConjectures.AlgebraicGeometry.ProEtaleLisseFiniteModelsFromLisse
import WeilConjectures.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction
import WeilConjectures.AlgebraicGeometry.ProfiniteCoefficientInverseImage
import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf

set_option linter.privateModule false

/-!
# Constructible pro-etale coefficients are of etale origin

Source: Weil blueprint, smooth purity, `theorem-comparison-constructible-sheaves`;
Stacks Project, Tags 09AK and 09AL (blueprint: theorem-comparison-constructible-sheaves).

The scalar conversion below is induced by constant scalar sections and sheafification.
It retains the recorded intrinsic constructibility predicate and the recorded category
of finite coefficient modules. Discrete topology is fixed canonically on lifted coefficients.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

variable (T : Scheme.{u}) (B : Type u) [CommRing B] [Finite B]

/-- The recorded canonical inverse image on module sheaves.
Source: blueprint, site comparison (blueprint: theorem-comparison-constructible-sheaves). -/
private theorem fixedDerivedOrigin (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} Λ)))
    (hc : ∀ q : ℤ, IsConstructible Λ
      ((DerivedCategory.homologyFunctor _ q).obj K))
    (a b : ℤ) (hz : ∀ q : ℤ, (q < a ∨ b < q) →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj K)) :
    ∃ L : Etale.DerivedCategoryModule Λ T,
      Etale.DerivedCategory.isBoundedConstructible Λ T L ∧
      Nonempty ((comparisonUpperStar (ModuleCat.{u + 1} Λ) T).mapDerivedCategory.obj L ≅ K) := by
  let ν := comparisonUpperStar (ModuleCat.{u + 1} Λ) T
  have : IsIso (derivedComparisonAdjunctionPlus (ModuleCat.{u + 1} Λ) T).unit :=
    isIso_compactSupportComparisonUnit T Λ
  have : ν.mapDerivedCategoryPlus.Full :=
    (derivedComparisonAdjunctionPlus (ModuleCat.{u + 1} Λ) T).fullyFaithfulLOfIsIsoUnit.full
  let F := ν.mapDerivedCategoryPlus ⋙ DerivedCategory.Plus.ι
  let P := ν.essImage
  have hP (G : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} Λ)) (hG : P G) :
      F.essImage ((DerivedCategory.singleFunctor _ 0).obj G) := by
    obtain ⟨H, ⟨e⟩⟩ := hG
    refine ⟨(DerivedCategory.Plus.singleFunctor _ 0).obj H, ⟨?_⟩⟩
    exact (ν.mapDerivedCategoryPlusCompatibility.app _) ≪≫
      ν.mapDerivedCategory.mapIso ((DerivedCategory.Plus.singleFunctorιIso _ 0).app H) ≪≫
      (ν.mapDerivedCategorySingleFunctor 0).app H ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso e
  have hGE : K.IsGE a := (DerivedCategory.isGE_iff K a).mpr
    (fun q hq ↦ hz q (Or.inl hq))
  have hLE : K.IsLE b := (DerivedCategory.isLE_iff K b).mpr
    (fun q hq ↦ hz q (Or.inr hq))
  have hK : F.essImage K := DerivedCategory.prop_of_bounded F.essImage P hP K
    ⟨⟨a, hGE⟩, ⟨b, hLE⟩⟩ (fun q ↦ by
      obtain ⟨G, _, he⟩ := exists_isConstructibleSheaf_iso_comparisonUpperStar_obj Λ (hc q)
      exact ⟨G, he⟩)
  obtain ⟨L, ⟨e⟩⟩ := hK
  let e' : ν.mapDerivedCategory.obj L.obj ≅ K :=
    (ν.mapDerivedCategoryPlusCompatibility.app L).symm ≪≫ e
  refine ⟨L.obj, ⟨?_, ?_⟩, ⟨e'⟩⟩
  · intro q
    have hq := isConstructible_of_iso
      ((DerivedCategory.homologyFunctor _ q).mapIso e'.symm) (hc q)
    have hν := isConstructible_of_iso
      ((ν.mapDerivedCategoryHomologyFunctorIso q).symm.app L.obj) hq
    obtain ⟨G, hG, ⟨eG⟩⟩ :=
      exists_isConstructibleSheaf_iso_comparisonUpperStar_obj Λ hν
    have : Scheme.IsConstructibleSheaf G := hG
    exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
      (Scheme.IsConstructibleSheaf.of_iso (ν.preimageIso eG))
  · refine ⟨min a b, b, min_le_right _ _, fun q hq ↦ ?_⟩
    apply ν.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
    exact (hz q (hq.imp (fun h ↦ lt_of_lt_of_le h (min_le_left _ _)) id)).of_iso
      ((DerivedCategory.homologyFunctor _ q).mapIso e')

end AlgebraicGeometry.ProEtale

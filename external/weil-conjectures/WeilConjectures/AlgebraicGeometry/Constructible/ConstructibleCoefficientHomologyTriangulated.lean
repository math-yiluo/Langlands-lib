/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleCoefficientSheaf

import WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleCoefficientSerre
import WeilConjectures.CategoryTheory.SmoothBaseChange.CohomologyInWeakSerreSubcategory
import WeilConjectures.AlgebraicGeometry.CompletedConstantReduction.CompletedConstantSheafReductionSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageCanonicalUnit
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
import WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import WeilConjectures.CategoryTheory.ModuleInverseImageAction
import Mathlib.Algebra.Category.Ring.Limits
import WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction

/-! # Constructible cohomology with coefficients in the site universe
Source: Stacks Tags 09B5, 093U and 06UQ.
(blueprint: lem-weil-constructible-coefficient-homology-triangulated). -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

private theorem coefficientConstructible_of_iso
    (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] [Finite A]
    {F G : pbcModules T (adicLisseConstantRing T A)} (e : F ≅ G)
    (hF : IsConstructibleProEtaleCoefficientModuleSheaf T A F) :
    IsConstructibleProEtaleCoefficientModuleSheaf T A G := by
  obtain ⟨S, hn, hc, h⟩ := hF
  refine ⟨S, hn, hc, fun i ↦ ?_⟩
  obtain ⟨V, hV, htriv⟩ := h i
  refine ⟨V, hV, fun U f hf ↦ ?_⟩
  obtain ⟨M, hM, ⟨eM⟩⟩ := htriv U f hf
  refine ⟨M, hM, ⟨?_⟩⟩
  exact (SheafOfModules.overFunctor _ U).mapIso
    ((proEtaleModuleInverseImage (S.immersion i) (adicLisseConstantRing T A)).mapIso
      e.symm) ≪≫ eM

private theorem coefficientConstant_isZero
    (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (M : ModuleCat.{u + 1} A) (hM : Limits.IsZero M) :
    Limits.IsZero ((adicLisseConstantModules T A).obj M) := by
  have := CompletedConstantReduction.constant_additive T A
  exact (adicLisseConstantModules T A).map_isZero hM

private theorem coefficientInverseImage_isZero
    {T Y : Scheme.{u}} (g : Y ⟶ T)
    (A : Type (u + 1)) [CommRing A]
    (F : pbcModules T (adicLisseConstantRing T A)) (hF : Limits.IsZero F) :
    Limits.IsZero ((proEtaleModuleInverseImage g (adicLisseConstantRing T A)).obj F) := by
  obtain ⟨adj, _⟩ := proEtaleModuleInverseImage_canonicalUnitComparison g
    (adicLisseConstantRing T A)
  have := adj.isLeftAdjoint
  exact (proEtaleModuleInverseImage g (adicLisseConstantRing T A)).map_isZero hF

private theorem coefficientConstructible_of_isZero
    (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] [Finite A]
    (F : pbcModules T (adicLisseConstantRing T A)) (hF : Limits.IsZero F) :
    IsConstructibleProEtaleCoefficientModuleSheaf T A F := by
  let S : Stratification T :=
    { n := 1
      stratum := fun _ ↦ Set.univ
      isLocallyClosed_stratum := fun _ ↦ IsOpen.isLocallyClosed isOpen_univ
      isConstructible_stratum := fun _ ↦ Topology.IsConstructible.univ
      iUnion_stratum_eq_univ := by
        ext x
        exact ⟨fun _ ↦ Set.mem_univ _, fun _ ↦ Set.mem_iUnion.mpr ⟨0, Set.mem_univ _⟩⟩
      pairwise_disjoint_stratum := fun i j h ↦ (h (Subsingleton.elim i j)).elim
      domain := fun _ ↦ T
      immersion := fun _ ↦ 𝟙 T
      range_immersion := fun _ ↦ Set.range_id }
  refine ⟨S, Nat.zero_lt_succ 0, fun _ ↦ Topology.IsConstructible.univ, fun i ↦ ?_⟩
  refine ⟨⊤, GrothendieckTopology.top_mem _ _, fun V f _ ↦ ?_⟩
  let : Zero (ModuleCat.{u + 1} A) := Limits.HasZeroObject.zero' _
  have : Subsingleton (0 : ModuleCat.{u + 1} A) :=
    ModuleCat.subsingleton_of_isZero (Limits.isZero_zero _)
  refine ⟨0, inferInstance, ⟨?_⟩⟩
  have h₁ := coefficientInverseImage_isZero (S.immersion i) A F hF
  have h₂ := coefficientInverseImage_isZero (S.immersion i) A _
    (coefficientConstant_isZero T A 0 (Limits.isZero_zero _))
  let G := SheafOfModules.overFunctor
    ((adicLisseForget (S.domain i)).obj
      ((proEtaleSheafInverseImage (S.immersion i) CommRingCat.{u + 1}).obj
        (adicLisseConstantRing T A))) V
  have : G.PreservesZeroMorphisms := ⟨fun _ _ ↦ rfl⟩
  exact (G.map_isZero h₁).iso (G.map_isZero h₂)

/-- Intrinsically constructible cohomology is an isomorphism-closed triangulated
property, with no boundedness hypothesis and coefficients in Type (u+1).
Source: Stacks Tags 09B5, 093U and 06UQ; the coefficient-universe version of the
finite-level argument (blueprint: lem-weil-constructible-coefficient-homology-triangulated).
Proof: refine two finite locally closed stratifications by their intersections.
Exact inverse image identifies kernels and cokernels with those of restricted maps.
Locally constant finite modules over a finite ring form a Serre class: finite-type
locally constant closure applies since the ring is Noetherian, and finite generation
over a finite ring gives finite underlying sets. The same refinement proves extension
closure. Zero has the one empty stratum on the empty scheme, and one whole stratum
otherwise. Transport local trivializations along isomorphisms. Thus the sheaf property
contains zero and is closed under isomorphisms, kernels, cokernels and extensions.
Apply the derived homology-property instances (Stacks 06UQ). The size of the finite
ring never enters this argument; all local module carriers have universe u+1. -/
theorem constructibleCoefficientHomology_isTriangulated
    (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] [Finite A] :
    ObjectProperty.IsClosedUnderIsomorphisms
      (DerivedCategory.homologyProperty (IsConstructibleProEtaleCoefficientModuleSheaf T A)) ∧
    ObjectProperty.IsTriangulated
      (DerivedCategory.homologyProperty (IsConstructibleProEtaleCoefficientModuleSheaf T A)) := by
  let P : ObjectProperty (pbcModules T (adicLisseConstantRing T A)) :=
    IsConstructibleProEtaleCoefficientModuleSheaf T A
  let : Zero (pbcModules T (adicLisseConstantRing T A)) := Limits.HasZeroObject.zero' _
  have : P.IsClosedUnderIsomorphisms :=
    ⟨fun e h ↦ coefficientConstructible_of_iso T A e h⟩
  have : P.ContainsZero :=
    ⟨0, Limits.isZero_zero _, coefficientConstructible_of_isZero T A _ (Limits.isZero_zero _)⟩
  obtain ⟨hkc, hext⟩ := constructibleCoefficient_exactClosure T A
  have : P.IsClosedUnderKernels := ⟨by
    rintro _ ⟨f, k, hk, hFG⟩
    exact P.prop_of_iso ((Limits.kernelIsKernel f).conePointUniqueUpToIso hk)
      (hkc _ _ f hFG.1 hFG.2).1⟩
  have : P.IsClosedUnderCokernels := ⟨by
    rintro _ ⟨f, k, hk, hFG⟩
    exact P.prop_of_iso ((Limits.cokernelIsCokernel f).coconePointUniqueUpToIso hk)
      (hkc _ _ f hFG.1 hFG.2).2⟩
  have : P.IsClosedUnderExtensions := ⟨fun hS h₁ h₃ ↦ hext _ hS h₁ h₃⟩
  exact ⟨inferInstance, (cohomology_in_weak_serre_subcategory P).1⟩

end AlgebraicGeometry.Scheme

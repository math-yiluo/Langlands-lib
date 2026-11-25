/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedModuleConstructible
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.ProEtaleLisseFiniteModelsFromLisse
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleFixedModuleLocalConstancy
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelStalks
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Point.Over
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelLocalConstancy
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence
import Mathlib.CategoryTheory.Functor.TypeValuedFlat
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison

/-! # Object comparison for exceptional transport

Source: blueprint main-20261015, the final restriction paragraph of
`theorem-f-shriek-finite-coefficients`, transport Steps 1 and 2.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale

private theorem empty_finiteLocal (T : Scheme.{u}) [IsEmpty T]
    (A : Type (u + 1)) [CommRing A]
    (F : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) :
    IsFiniteLocallyConstant A F := by
  refine ⟨ULift.{u + 1} Empty, fun i ↦ i.down.elim, fun i ↦ i.down.elim, ?_,
    fun i ↦ i.down.elim⟩
  have he : Presieve.ofArrows (fun i : ULift.{u + 1} Empty ↦ i.down.elim)
      (fun i ↦ i.down.elim) = (⊥ : Presieve T) := by
    funext U f
    apply propext
    constructor
    · rintro ⟨i⟩
      exact i.down.elim
    · exact False.elim
  rw [he]
  exact Scheme.bot_mem_propQCPrecoverage T

private def identityStratification (T : Scheme.{u}) : Scheme.Stratification T where
  n := 1
  stratum _ := Set.univ
  isLocallyClosed_stratum _ := isOpen_univ.isLocallyClosed
  isConstructible_stratum _ := Topology.IsConstructible.univ
  iUnion_stratum_eq_univ := by
    apply Set.eq_univ_of_forall
    intro x
    exact Set.mem_iUnion.mpr ⟨0, Set.mem_univ x⟩
  pairwise_disjoint_stratum i j hij := (hij (Subsingleton.elim _ _)).elim
  domain _ := T
  immersion _ := 𝟙 T
  range_immersion _ := Set.range_id

private theorem fixed_constructible_iff
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (F : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) :
    Scheme.IsConstructibleProEtaleFixedModuleSheaf T A F ↔ IsConstructible A F := by
  have hlocal (T : Scheme.{u})
      (F : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))
      (hF : IsFiniteLocallyConstant A F) :
      Scheme.IsLocallyConstantProEtaleFixedModuleSheaf T A F ∧
        ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ T),
          Finite (Scheme.proEtaleGeometricFixedModuleStalk x A F) := by
    replace hF : ∃ (ι : Type (u + 1)) (W : ι → Scheme.{u}) (g : ∀ i, W i ⟶ T),
        Presieve.ofArrows W g ∈ Scheme.proetalePrecoverage T ∧
          ∀ i, ∃ M : ModuleCat.{u + 1} A, Finite M ∧
            Nonempty (((g i)^*[ModuleCat.{u + 1} A]).obj F ≅
              (constantSheaf (Scheme.ProEt.topology (W i)) (ModuleCat.{u + 1} A)).obj M) := by
      obtain ⟨ι, W, g, hg, h⟩ := hF
      refine ⟨ι, W, g, hg, fun i ↦ ?_⟩
      obtain ⟨M, hM, e⟩ := h i
      exact ⟨M, Module.finite_of_finite A, e⟩
    obtain ⟨I, U, f, hf, he⟩ := finiteModels_over A F hF
    refine ⟨⟨I, U, f, hf, fun i ↦ ?_⟩,
      fun Ω _ _ x ↦ finite_geometricStalk_of_finite_models A F hF Ω x⟩
    obtain ⟨M, _, hM⟩ := he i
    exact ⟨M, hM⟩
  constructor
  · rintro ⟨S, _, _, hS⟩
    refine ⟨S, fun i ↦ ?_⟩
    obtain ⟨ι, W, g, hg, h⟩ := Scheme.finite_models_of_fixed_lisse (S.domain i) A _ (hS i)
    refine ⟨ι, W, g, hg, fun j ↦ ?_⟩
    obtain ⟨M, _, e⟩ := h j
    exact ⟨M, Module.Finite.of_finite, e⟩
  · rintro ⟨S, hS⟩
    by_cases hn : 0 < S.n
    · exact ⟨S, hn, S.isConstructible_stratum, fun i ↦ hlocal _ _ (hS i)⟩
    have hz : S.n = 0 := Nat.eq_zero_of_not_pos hn
    have : IsEmpty T := ⟨fun x ↦ by
      have hx : x ∈ ⋃ i, S.stratum i := S.iUnion_stratum_eq_univ.symm ▸ Set.mem_univ x
      obtain ⟨i, _⟩ := Set.mem_iUnion.mp hx
      exact Fin.elim0 (hz ▸ i)⟩
    exact ⟨identityStratification T, Nat.zero_lt_one,
      (identityStratification T).isConstructible_stratum,
      fun i ↦ hlocal _ _ (empty_finiteLocal T A _)⟩

private theorem etale_boundedConstructible_iff
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (K : Etale.DerivedCategoryModule A T) :
    Etale.DerivedCategory.isBoundedConstructible A T K ↔
      Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) T K := by
  constructor
  · rintro ⟨hc, a, b, _, h⟩
    exact ⟨⟨⟨a, (_root_.DerivedCategory.isGE_iff K a).mpr
      (fun i hi ↦ h i (Or.inl hi))⟩,
      ⟨b, (_root_.DerivedCategory.isLE_iff K b).mpr
        (fun i hi ↦ h i (Or.inr hi))⟩⟩,
      fun i ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (hc i)⟩
  · rintro ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩
    refine ⟨fun i ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
      (hc i), min a b, b, min_le_right _ _, ?_⟩
    intro i hi
    rcases hi with hi | hi
    · exact (_root_.DerivedCategory.isGE_iff K a).mp ha i
        (lt_of_lt_of_le hi (min_le_left _ _))
    · exact (_root_.DerivedCategory.isLE_iff K b).mp hb i hi

/-- Intrinsic bounded constructible objects are precisely comparison images
of bounded constructible etale objects. The coefficient ring may be zero.
Source: blueprint main-20261015, `lem-sf-etale-proetale-exceptional-transport`,
Steps 1 and 2 (blueprint: new-etale-proetale-exceptional-object-comparison).

Proof: identify fixed-module constructibility with the finite constant-model predicate
using finite-model local constancy and geometric stalks in one direction, and finite
models for lisse sheaves in the other. If the original stratification has no strata,
the scheme is empty; use the one-stratum identity stratification and the empty cover.
Translate etale module constructibility to the source constructible-sheaf predicate,
and translate the explicit vanishing interval to boundedness for the canonical
t-structure. For the forward implication, each constructible cohomology sheaf has an
etale origin. The source bounded-constructible reconstruction theorem then supplies
an etale origin for the complex. Conversely, exact comparison commutes with homology,
preserves constructibility and boundedness, and these properties transport along the
origin isomorphism. Empty schemes, zero objects, and the zero ring are included. -/
theorem exceptionalTransport_constructible_comparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) [IsNoetherian T] :
    (fun K ↦ _root_.DerivedCategory.TStructure.t.bounded K ∧
      ∀ i : ℤ, Scheme.IsConstructibleProEtaleFixedModuleSheaf T A
        ((_root_.DerivedCategory.homologyFunctor _ i).obj K)) =
    (Etale.DerivedCategory.isBoundedConstructible A T).map
      (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory  := by
  let N := (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory
  let P := comparisonUpperStar (ModuleCat.{u + 1} A) T
  funext K
  apply propext
  constructor
  · rintro ⟨hb, hc⟩
    have h : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) T K := by
      apply DerivedCategory.boundedConstructible_of_homology A hb
      intro i
      obtain ⟨G, hG, ⟨e⟩⟩ :=
        exists_isConstructibleSheaf_iso_comparisonUpperStar_obj A
          ((fixed_constructible_iff A T _).mp (hc i))
      exact ⟨G, hG, ⟨e⟩⟩
    obtain ⟨H, hH, ⟨e⟩⟩ := h
    exact ⟨H, (etale_boundedConstructible_iff A T H).mpr hH, ⟨e⟩⟩
  · rintro ⟨H, hH, ⟨e⟩⟩
    have hH' := (etale_boundedConstructible_iff A T H).mp hH
    have hb := (DerivedCategory.boundedConstructible_comparisonUpperStar_mapDerivedCategory_obj
      hH').bounded
    refine ⟨_root_.DerivedCategory.TStructure.t.bounded.prop_of_iso e hb, fun i ↦ ?_⟩
    apply (fixed_constructible_iff A T _).mpr
    have : Scheme.IsConstructibleSheaf
        ((_root_.DerivedCategory.homologyFunctor _ i).obj H) := hH'.2 i
    exact isConstructible_of_iso
      ((P.mapDerivedCategoryHomologyFunctorIso i).app H ≪≫
        (_root_.DerivedCategory.homologyFunctor _ i).mapIso e)
      (isConstructible_comparisonUpperStar_obj _)

end AlgebraicGeometry.ProEtale

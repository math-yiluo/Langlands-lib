/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Free
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.AlgebraicGeometry.SiteLocallyConstantFiniteType
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.SiteBoundedTruncationModels
import WeilConjectures.CategoryTheory.LocalizedModuleAdjunctionExact
import WeilConjectures.RingTheory.NoetherianPseudoCoherentCohomologyCriterion

/-! # Local finite free models of a good lower truncation

Source: Stacks Project, Cohomology on Sites, Tags 094G and 094H; More on Algebra,
Tag 066E (auxiliary; not a blueprint node).
-/

@[expose] public section

universe u v w w'
open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

variable {C : Type u} [Category.{u} C]

set_option quotPrecheck false in
set_option hygiene false in
local notation "𝓡(" J ", " B ")" => (sheafCompose J
  (forget₂ CommRingCat.{u} RingCat.{u})).obj
    ((constantSheaf J CommRingCat.{u}).obj (CommRingCat.of B))
set_option quotPrecheck false in
set_option hygiene false in
local notation "cB(" J ", " B ")" => strictPerfectConstantPresheaf (C := C) B ⋙
  PresheafOfModules.sheafification.{u} (R := 𝓡(J, B)) (Functor.whiskerRight
    (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of B)))
    (forget₂ CommRingCat.{u} RingCat.{u}))

theorem constant_preservesFiniteLimits (B : Type u) [CommRing B] :
    PreservesFiniteLimits (SheafOfModules.strictPerfectConstantPresheaf (C := C) B) := by
  constructor
  intro D hD hfin
  constructor
  intro F
  constructor
  intro c hc
  refine ⟨PresheafOfModules.evaluationJointlyReflectsLimits _ _ (fun U ↦ ?_)⟩
  exact hc

theorem constant_preservesFiniteColimits (B : Type u) [CommRing B] :
    PreservesFiniteColimits (SheafOfModules.strictPerfectConstantPresheaf (C := C) B) := by
  constructor
  intro D hD hfin
  constructor
  intro F
  constructor
  intro c hc
  refine ⟨PresheafOfModules.evaluationJointlyReflectsColimits _ _ (fun U ↦ ?_)⟩
  exact hc

theorem finite_module_homology
    (B : Type u) [CommRing B] [IsNoetherianRing B]
    (T : CochainComplex (ModuleCat.{u} B) ℤ)
    (hT : ∀ j : ℤ, Module.Finite B (T.X j)) (i : ℤ) :
    Module.Finite B (T.homology i) := by
  have := hT i
  have : IsNoetherian B (T.cycles i) := isNoetherian_of_injective
    (T.iCycles i).hom ((ModuleCat.mono_iff_injective _).1 inferInstance)
  have : Module.Finite B (T.cycles i) := inferInstance
  exact Module.Finite.of_surjective (T.homologyπ i).hom
    ((ModuleCat.epi_iff_surjective _).1 inferInstance)

private theorem finite_free_realization (B : Type u) [CommRing B] [IsNoetherianRing B]
    [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    {A : Type v} [Category.{u} A] [Abelian A] [HasDerivedCategory.{w'} A]
    (F : ModuleCat.{u} B ⥤ A) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (T : CochainComplex (ModuleCat.{u} B) ℤ)
    (b : ℤ) (hb : ∀ j : ℤ, b < j → IsZero (T.X j))
    (hT : ∀ j : ℤ, Module.Finite B (T.X j)) :
    ∃ (E : CochainComplex (ModuleCat.{u} B) ℤ) (c : ℤ),
      (∀ j : ℤ, c < j → IsZero (E.X j)) ∧
      (∀ j : ℤ, Module.Free B (E.X j) ∧ Module.Finite B (E.X j)) ∧
      Nonempty (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj T) ≅
        DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj E)) := by
  have eH (j : ℤ) := (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} B) j).app T
  have hhom (j : ℤ) : Module.Finite B
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) j).obj (DerivedCategory.Q.obj T)) := by
    have : Module.Finite B
        ((HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (.up ℤ) j).obj T) :=
      finite_module_homology B T hT j
    exact Module.Finite.of_surjective (eH j).inv.hom
      ((ModuleCat.epi_iff_surjective _).1 inferInstance)
  have hvan (j : ℤ) (hj : b < j) : IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) j).obj
        (DerivedCategory.Q.obj T)) :=
    (HomologicalComplex.ExactAt.of_isZero (hb j hj)).isZero_homology.of_iso (eH j)
  obtain ⟨E, c, hEc, hE, ⟨e⟩⟩ :=
    (DerivedCategory.isPseudoCoherent_iff_boundedAbove_finite_homology B
      (DerivedCategory.Q.obj T)).2 ⟨⟨b, hvan⟩, hhom⟩
  let := hEc
  refine ⟨E, c, fun j hj ↦ E.isZero_of_isStrictlyLE c j hj, hE, ?_⟩
  exact ⟨(F.mapDerivedCategoryFactors.app T).symm ≪≫
    F.mapDerivedCategory.mapIso e.symm ≪≫ F.mapDerivedCategoryFactors.app E⟩

set_option synthInstance.maxSize 2048 in
/-- A single bounded-above complex with finite locally constant cohomology has, on
covering slices, bounded-above finite free constant models for each good lower truncation.
The derived categories of slices use their standard localization; no choice of small
localization or points of the site is required.

Source: Stacks Project, Tags 094G and 094H, the bounded-model and finite-free replacement
steps; More on Algebra, Tag 066E.
(auxiliary; not a blueprint node).

Proof: Fix the lower cutoff a and an upper cohomological bound b. Exact restriction
commutes with good truncation. The truncated object has finite locally constant
cohomology in [a,b] and zero cohomology elsewhere. If a > b it is zero and take the zero
module complex. Otherwise apply the local bounded constant model lemma on each slice,
whose terminal object is its identity arrow. Its module-valued sheaf presentation agrees
with modules over the constant ring sheaf by constant-ring sheafification. The constant
restriction comparison is natural in module maps, so the resulting model is the
restriction of the termwise global constant complex. A bounded finite-module complex has
finite cohomology by Noetherianity, hence is pseudo-coherent by Tag 066E. Choose its
bounded-above finite free representative and apply exact constant realization to its
derived isomorphism. Compose the two isomorphisms. Take the sieve generated by the
covering family; further restriction preserves the same constant model and its bound,
by relocalization and naturality of constant restriction. This proves the assertion for
every arrow of a covering sieve, including empty slices. -/
theorem exists_site_finiteFree_truncation_models
    (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (B : Type u) [CommRing B] [IsNoetherianRing B]
    (P : CochainComplex (SheafOfModules.{u} (𝓡(J.toGrothendieck, B))) ℤ)
    (hbounded : ∃ b : ℤ, ∀ j : ℤ, b < j → IsZero (P.homology j))
    (hlc : ∀ j : ℤ, IsLocallyConstantFiniteType J.toGrothendieck B (P.homology j))
    (a : ℤ) (V : C) :
    ∃ S : Sieve V, S ∈ J.toGrothendieck V ∧
      ∀ (U : C) (f : U ⟶ V), S f →
        let := HasDerivedCategory.standard (SheafOfModules.{u} ((𝓡(J.toGrothendieck, B)).over U))
        ∃ (E : CochainComplex (ModuleCat.{u} B) ℤ) (b : ℤ),
          (∀ j : ℤ, b < j → IsZero (E.X j)) ∧
          (∀ j : ℤ, Module.Free B (E.X j) ∧ Module.Finite B (E.X j)) ∧
          Nonempty
            (DerivedCategory.Q.obj
                (((overFunctor.{u} (𝓡(J.toGrothendieck, B)) U).mapHomologicalComplex
                  (.up ℤ)).obj (P.truncGE a)) ≅
              DerivedCategory.Q.obj
                ((((cB(J.toGrothendieck, B)) ⋙
                  overFunctor.{u} (𝓡(J.toGrothendieck, B)) U).mapHomologicalComplex
                    (.up ℤ)).obj E)) := by
  obtain ⟨S, hS, hmodels⟩ := exists_site_bounded_truncation_models J B P hbounded hlc a V
  refine ⟨S, hS, ?_⟩
  intro U f hf
  let := HasDerivedCategory.standard (SheafOfModules.{u} ((𝓡(J.toGrothendieck, B)).over U))
  let := HasDerivedCategory.standard (ModuleCat.{u} B)
  obtain ⟨M, bM, hMb, hM, ⟨eM⟩⟩ := hmodels U f hf
  let := constant_preservesFiniteLimits (C := C) B
  let := constant_preservesFiniteColimits (C := C) B
  have : PreservesFiniteLimits (cB(J.toGrothendieck, B)) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (cB(J.toGrothendieck, B)) := comp_preservesFiniteColimits _ _
  have hres := localizedModule_adjunction_exact J
    ((constantSheaf J.toGrothendieck CommRingCat.{u}).obj (CommRingCat.of B)) U
  have := hres.1
  have := hres.2.1
  let F := cB(J.toGrothendieck, B) ⋙ overFunctor.{u} (𝓡(J.toGrothendieck, B)) U
  have : PreservesFiniteLimits F := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits F := comp_preservesFiniteColimits _ _
  have : F.Additive := Functor.additive_of_preserves_binary_products F
  obtain ⟨E, bE, hEb, hE, ⟨eE⟩⟩ := finite_free_realization B F M bM
    (fun j hj ↦ hMb j (Or.inr hj)) hM
  exact ⟨E, bE, hEb, hE, ⟨eM ≪≫ eE⟩⟩

end SheafOfModules

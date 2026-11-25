/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralStratum
import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralGluing
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralScalarExact

/-! # Integral models for constructible sheaves in degree zero

Source: Bhatt--Scholze, Lemma 6.8.13 and the sheaf case of Proposition 6.8.14(2).
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

private lemma constructible_zero_local {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    [MonObj R] (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)
    (hM : Limits.IsZero M) : ProEtale.IsConstructibleModuleObject R M := by
  let S : Scheme.Stratification X :=
    { n := 1
      stratum := fun _ ↦ Set.univ
      isLocallyClosed_stratum := fun _ ↦ isOpen_univ.isLocallyClosed
      isConstructible_stratum := fun _ ↦ Topology.IsConstructible.univ
      iUnion_stratum_eq_univ := Set.iUnion_const _
      pairwise_disjoint_stratum := fun i j hij ↦ (hij (Subsingleton.elim i j)).elim
      domain := fun _ ↦ X
      immersion := fun _ ↦ 𝟙 X
      range_immersion := fun _ ↦ Set.range_id' }
  refine ⟨S, fun a ↦ ?_⟩
  let U : Scheme.Cover.{u} Scheme.proetalePrecoverage (S.domain a) :=
    Precoverage.ZeroHypercover.singleton (𝟙 (S.domain a))
    (Precoverage.mem_coverings_of_isIso _)
  refine ⟨U, fun i ↦ ?_⟩
  have hSa := ((ProEtale.upperStar Ab.{u + 1} (S.immersion a)).mapMod R).map_isZero hM
  have hUi := ((ProEtale.upperStar Ab.{u + 1} (U.f i)).mapMod
    ((ProEtale.upperStar Ab.{u + 1} (S.immersion a)).obj R)).map_isZero hSa
  refine ⟨0, 0, 𝟙 _, ⟨?_⟩⟩
  exact hUi.iso (Limits.isZero_cokernel_of_epi (𝟙 _))

private lemma finitePresentation_of_iso_local {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (e : M ≅ N) (hM : Mod.IsFinitelyPresented R M) :
    Mod.IsFinitelyPresented R N := by
  obtain ⟨n, m, g, ⟨eg⟩⟩ := hM
  exact ⟨n, m, g, ⟨e.symm ≪≫ eg⟩⟩

private lemma localFinitePresentation_of_iso_local {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R} (e : M ≅ N)
    (hM : ProEtale.IsLocallyFinitelyPresented R M) :
    ProEtale.IsLocallyFinitelyPresented R N := by
  obtain ⟨U, hU⟩ := hM
  refine ⟨U, fun i ↦ ?_⟩
  exact finitePresentation_of_iso_local
    (((ProEtale.upperStar Ab.{u + 1} (U.f i)).mapMod R).mapIso e) (hU i)

private lemma constructible_of_iso_local {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R} (e : M ≅ N)
    (hM : ProEtale.IsConstructibleModuleObject R M) :
    ProEtale.IsConstructibleModuleObject R N := by
  obtain ⟨S, hS⟩ := hM
  refine ⟨S, fun a ↦ ?_⟩
  exact localFinitePresentation_of_iso_local
    (((ProEtale.upperStar Ab.{u + 1} (S.immersion a)).mapMod R).mapIso e) (hS a)

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
  [FiniteDimensional ℚ_[ℓ] E]

/-- A constructible continuous E module, placed in degree zero, has an integral model.
Source: Bhatt--Scholze, Lemmas 6.8.12--6.8.13 and Proposition 6.8.14(2).
(auxiliary; not a blueprint node)

Proof in words. On each of the finitely many constructible strata, identify local finite
presentations over the continuous E coefficient sheaf with finite-rank local systems.
Lemma 6.8.13 supplies a constructible integral lattice on that stratum. Refine the
stratification to a finite filtration by closed subsets, and use the open--closed exact
sequences to reconstruct the sheaf from the extensions by zero of its restrictions.
These exact extension functors preserve integral constructibility. To lift an extension
between two integral models, Lemma 6.8.12 identifies its rational Ext1 group with the
localization of integral Ext1. Multiply the extension class by a power of ℓ to lift it;
that scalar is invertible over E, so the new extension rationalizes to the original one.
Induction through the finite filtration gives a constructible integral sheaf whose
rationalization is the given module. Place it in degree zero. Exactness of coefficient
localization identifies this with derived integralScalarExtension. The compact profinite
continuous-function localization calculation, pulled back from the point, identifies the
coefficient map with the actual one used here. The zero sheaf and empty scheme use zero.
-/
theorem continuousConstructible_integral_single_model (X : Scheme.{u})
    [TopologicalSpace.NoetherianSpace X]
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    (hF : ProEtale.IsConstructibleModuleObject
      (condensedRingObj (Profinite.continuousMapRingObj E) X) F) :
    ∃ M : integralConstructible ℓ E X,
      Nonempty ((integralScalarExtension ℓ E X).obj M.obj ≅
        (DerivedCategory.singleFunctor _ 0).obj F) := by
  obtain ⟨S, hS⟩ := hF
  have hmodels := fun a ↦ continuousConstructible_integral_stratum ℓ E X
    (S.immersion a) _ (hS a)
  obtain ⟨N, hN, ⟨e⟩⟩ := continuousConstructible_integral_gluing ℓ E X F S hmodels
  let K : integralConstructible ℓ E X :=
    ⟨(DerivedCategory.singleFunctor _ 0).obj N, by
      rw [ProEtale.mem_boundedConstructible_iff]
      refine ⟨⟨0, 0, ?_⟩, ?_⟩
      · intro i hi
        rcases hi with hi | hi
        · exact DerivedCategory.isZero_of_isGE _ 0 i hi
        · exact DerivedCategory.isZero_of_isLE _ 0 i hi
      · intro i
        rcases eq_or_ne i 0 with rfl | hi
        · exact constructible_of_iso_local
            ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app N).symm hN
        · rcases lt_or_gt_of_ne hi with hi | hi
          · exact constructible_zero_local _ _ (DerivedCategory.isZero_of_isGE _ 0 i hi)
          · exact constructible_zero_local _ _ (DerivedCategory.isZero_of_isLE _ 0 i hi)⟩
  refine ⟨K, ⟨?_⟩⟩
  exact (Functor.singleFunctorCompLeftDerivedFunctorIso
    (Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X))).app N ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso e

end AlgebraicGeometry.ProEtale.CondensedRing

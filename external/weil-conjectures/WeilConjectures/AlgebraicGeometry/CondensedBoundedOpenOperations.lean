/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
import all WeilConjectures.AlgebraicGeometry.Open.OpenImmersionLocalizing
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback

/-! # Open operations on bounded constant-model constructible complexes -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

/-- Open extension and restriction preserve bounded constant-model constructibility,
without a finite-Tor assumption on their inputs.
Source: current blueprint def-fix-six-functor-datum and its open factor;
the finite-stratification extension-by-zero construction
(blueprint: lem-e6-condensed-bounded-open-operations).

Proof: the exact extension functor preserves the cohomological bounds. Extend
each finite stratification of a cohomology sheaf by its closed complement, on
which extension by zero is zero and hence has a finite constant model. The
homology comparison for an exact derived functor identifies these cohomology
sheaves with those of the derived extension. For restriction, pull back each
stratification and each finite constant local model; exactness again preserves
bounds and identifies cohomology. No Tor-amplitude condition is used. -/
theorem condensedBoundedOpenOperations
    (ℓ : ℕ) [Fact ℓ.Prime] (p : ℕ) [Fact p.Prime] (hpℓ : p ≠ ℓ)
    (k : Type u) [Field k] [CharP k p]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {U X : Scheme.{u}} [U.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (j : U ⟶ X) [IsOpenImmersion j] [j.IsOver (Spec (.of k))] :
    (∀ K : ConstantModelBoundedConstructible Λ U,
      constantModelBoundedConstructible Λ X
        ((CondensedRing.openImmersionLowerShriek Λ j).mapDerivedCategory.obj K.obj)) ∧
    (∀ K : ConstantModelBoundedConstructible Λ X,
      constantModelBoundedConstructible Λ U
        ((CondensedRing.upperStar Λ j).leftDerivedFunctor.obj K.obj)) := by
  let : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace
    (U ↘ Spec (.of k))
  let : QuasiSeparatedSpace U := quasiSeparatedSpace_of_quasiSeparated
    (U ↘ Spec (.of k))
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace
    (X ↘ Spec (.of k))
  let : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated
    (X ↘ Spec (.of k))
  constructor
  · intro K
    refine ⟨(CondensedRing.openImmersionLowerShriek Λ j).bounded_mapDerivedCategory_obj
      K.property.1, ?_⟩
    intro n
    have hU : CompactSpace U ∧ QuasiSeparatedSpace U := ⟨inferInstance, inferInstance⟩
    have hH := K.property.2 n
    rw [IsConstantModelConstructible, ite_eq_left hU] at hH
    obtain ⟨S, hcon, hS⟩ := finiteStratification_of_models
      (fun T f ↦ HasFiniteConstantLocalModel Λ T
        ((CondensedRing.upperStar Λ f).obj
          ((DerivedCategory.homologyFunctor _ n).obj K.obj))) hH
    have hc := (constantModelConstructible_openImmersionLowerShriek ℓ p hpℓ k Λ j
      ((DerivedCategory.homologyFunctor _ n).obj K.obj) S hcon hS).1
    exact constantModelConstructible_of_iso Λ
      (((CondensedRing.openImmersionLowerShriek Λ j).mapDerivedCategoryHomologyFunctorIso n).app
        K.obj) hc
  · intro K
    exact pullback_bounded_constructible Λ j
      (fun M hM ↦ pullback_constructible Λ j M hM) K.obj K.property

end AlgebraicGeometry.ProEtale

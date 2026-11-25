/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.UnboundedDirectImageComparisonMap
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Unbounded comparison of direct images for finite coefficients

For schemes of finite type over a finite or algebraically closed field `k` and a finite
`ℓ`-primary coefficient ring `A`, the comparison map `ν_Y^* Rg_* K ⟶ Rg_* ν_X^* K` is an
isomorphism for every unbounded complex `K` of étale sheaves. The bounded below case is
`AlgebraicGeometry.ProEtale.unboundedDirectImageComparison_boundedBelow`.

## Implementation details

The unbounded statement is not formalised yet and is recorded with `sorry`. Its proof reduces,
degree by degree, to the bounded below case by the uniform cohomological bounds on pro-étale
affines.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-- **Unbounded comparison of direct images for finite coefficients**: let `k` be a finite or
algebraically closed field, `ℓ` a prime invertible in `k`, `A` a finite `ℓ`-primary ring and
`g : X ⟶ Y` a morphism of schemes of finite type over `k`. For every
`K ∈ D(X_ét, A)`, the comparison map `ν_Y^* Rg_* K ⟶ Rg_* ν_X^* K`
(`AlgebraicGeometry.ProEtale.unboundedDirectImageComparisonMap`) is an isomorphism. -/
theorem isIso_unboundedDirectImageComparisonMap
    (k : Type u) [Field k] (hbase : Finite k ∨ IsAlgClosed k)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (algebraMap ℤ k (ℓ : ℤ)))
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : ∃ r : ℕ, (ℓ : A) ^ r = 0)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (g : X ⟶ Y) [g.IsOver (Spec (.of k))]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    IsIso (unboundedDirectImageComparisonMap A g K) := by
  sorry

end AlgebraicGeometry.ProEtale

/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.FieldTheory.Galois.Infinite

/-!
# Galois descent for polynomials

A polynomial over a (possibly infinite) Galois extension `L / K` whose coefficients are fixed by
`Gal(L / K)` has coefficients in `K`.
-/

@[expose] public section

namespace MvPolynomial

/-- A polynomial over a Galois extension `L / K` whose coefficients are fixed by `Gal(L / K)`
is defined over `K`. -/
theorem exists_map_algebraMap_eq_of_forall_map_eq {K L σ : Type*} [Field K] [Field L]
    [Algebra K L] [IsGalois K L] (p : MvPolynomial σ L)
    (hp : ∀ τ : L ≃ₐ[K] L, map (τ : L →+* L) p = p) :
    ∃ q : MvPolynomial σ K, map (algebraMap K L) q = p := by
  refine mem_range_map_iff_coeffs_subset.mpr fun c hc => ?_
  obtain ⟨m, -, rfl⟩ := mem_coeffs_iff.mp hc
  refine (InfiniteGalois.mem_range_algebraMap_iff_fixed _).mpr fun τ => ?_
  have h := congrArg (fun q : MvPolynomial σ L ↦ q.coeff m) (hp τ)
  rwa [coeff_map] at h

end MvPolynomial

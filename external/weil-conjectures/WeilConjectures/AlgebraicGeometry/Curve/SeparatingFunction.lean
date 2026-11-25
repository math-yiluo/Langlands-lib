/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Unramified.Basic
public import WeilConjectures.Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-!
# Separating rational functions on smooth curves

Let `X` be an integral scheme smooth of relative dimension one over a field `k`, with function
field `K = k(X)`. Then `Ω[K⁄k]` is a one-dimensional `K`-vector space. A rational function `t`
with `dt ≠ 0` spans it, so that `K` is formally unramified over every subring containing `t`;
such a `t` can be chosen transcendental over `k`.

## Main statements

- `Algebra.FormallyUnramified.of_finrank_kaehlerDifferential_eq_one`: if `Ω[K⁄R]` is
  one-dimensional and `D t ≠ 0` for some `t` in the image of `A`, then `K` is formally
  unramified over `A`.
- `exists_transcendental_and_D_ne_zero`: if `Ω[K⁄R]` is one-dimensional and `K` has an element
  transcendental over `k`, then it has one `t` with `D t ≠ 0`.
-/

@[expose] public section

universe u

open CategoryTheory KaehlerDifferential

section Algebra

/-- If `Ω[K⁄R]` is one-dimensional over the field `K` and `D t ≠ 0` for some `t` in the image of
an intermediate ring `A`, then `K` is formally unramified over `A`: `Ω[K⁄A]` is the quotient of
`Ω[K⁄R] = K ⬝ D t` by the differentials of elements of `A`. -/
theorem Algebra.FormallyUnramified.of_finrank_kaehlerDifferential_eq_one {R A K : Type*}
    [CommRing R] [CommRing A] [Field K] [Algebra R A] [Algebra A K] [Algebra R K]
    [IsScalarTower R A K] (h : Module.finrank K Ω[K⁄R] = 1) {t : K} (ht : D R K t ≠ 0)
    (htA : t ∈ Set.range (algebraMap A K)) : Algebra.FormallyUnramified A K := by
  refine ⟨subsingleton_of_forall_eq 0 fun x ↦ ?_⟩
  obtain ⟨y, rfl⟩ := KaehlerDifferential.map_surjective R A K x
  obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_nonzero' _ ht).mp h y
  obtain ⟨a, rfl⟩ := htA
  rw [LinearMap.map_smul, KaehlerDifferential.map_D, Algebra.algebraMap_self, RingHom.id_apply,
    Derivation.map_algebraMap, smul_zero]

/-- If `Ω[K⁄R]` is one-dimensional over the field `K` and `K` has an element transcendental over
a field `k`, then `K` has an element `t` transcendental over `k` with `D t ≠ 0`. -/
theorem exists_transcendental_and_D_ne_zero {k R K : Type*} [Field k] [CommRing R] [Field K]
    [Algebra k K] [Algebra R K] (h : Module.finrank K Ω[K⁄R] = 1) {s : K}
    (hs : Transcendental k s) : ∃ t : K, Transcendental k t ∧ D R K t ≠ 0 := by
  obtain ⟨u, hu⟩ : ∃ u : K, D R K u ≠ 0 := by
    by_contra! H
    have : (⊤ : Submodule K Ω[K⁄R]) = ⊥ := by
      rw [← KaehlerDifferential.span_range_derivation, Submodule.span_eq_bot]
      rintro _ ⟨u, rfl⟩
      exact H u
    have : Subsingleton Ω[K⁄R] := subsingleton_of_forall_eq 0 fun x ↦ by
      simpa using (this ▸ Submodule.mem_top : x ∈ (⊥ : Submodule K Ω[K⁄R]))
    simp [Module.finrank_zero_of_subsingleton] at h
  by_cases hDs : D R K s = 0
  swap
  · exact ⟨s, hs, hDs⟩
  by_cases hut : Transcendental k u
  · exact ⟨u, hut, hu⟩
  rw [Transcendental, not_not] at hut
  have hs0 : s ≠ 0 := fun h0 ↦ hs (h0 ▸ isAlgebraic_zero)
  have hu0 : u ≠ 0 := fun h0 ↦ hu (by rw [h0, map_zero])
  refine ⟨u * s, fun halg ↦ hs ?_, ?_⟩
  · have : s = u * s * u⁻¹ := by field_simp
    rw [this]
    exact halg.mul hut.inv
  · rw [Derivation.leibniz, hDs, smul_zero, zero_add]
    exact smul_ne_zero hs0 hu

end Algebra

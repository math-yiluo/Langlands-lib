/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.DirectSum.LinearMap
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.LinearAlgebra.Eigenspace.Zero
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import WeilConjectures.Mathlib.Algebra.Polynomial.Reverse
public import WeilConjectures.Mathlib.LinearAlgebra.Charpoly.ToMatrix

/-!
# Eigenvalues of an endomorphism of a vector space over an algebraically closed field

Over an algebraically closed field the characteristic polynomial of an endomorphism of a finite
dimensional vector space splits. This file records the descriptions of the characteristic
polynomial, of its reverse, of the determinant and of the traces of the powers that follow, all
in terms of the roots of the characteristic polynomial counted with multiplicity.

## Main results

- `LinearMap.charpoly_eq_prod_roots`: the characteristic polynomial of `f` is `∏ (X - λ)`.
- `LinearMap.charpolyRev_eq_prod_roots`: its reverse is `∏ (1 - λ * X)`.
- `LinearMap.card_roots_charpoly`: the number of roots is the dimension of the space.
- `LinearMap.det_eq_prod_roots_charpoly`: the determinant of `f` is the product of the roots; in
  particular `0` is not a root as soon as `f` is invertible, which is
  `LinearMap.zero_notMem_roots_charpoly`.
- `LinearMap.trace_pow_eq_sum_pow_roots_charpoly` and its matrix counterpart
  `Matrix.trace_pow_eq_sum_pow_roots_charpoly`: the trace of the `m`-th power is the `m`-th power
  sum `∑ λ ^ m` of the roots.
- `LinearMap.trace_pow_eq_of_charpoly_eq`: these traces only depend on the characteristic
  polynomial.
- `Matrix.charpolyRev_eq_prod_one_sub_smul`: the reciprocal characteristic polynomial
  `det (1 - t • A)` of a matrix is `∏ (1 - λ * t)`.
-/

@[expose] public section

open Module Polynomial Set

/-- If `x - μ` is nilpotent, then so is `x ^ m - μ ^ m`: the polynomial `X ^ m - μ ^ m` is
divisible by `X - μ`. -/
private theorem isNilpotent_pow_sub_algebraMap_pow {R A : Type*} [CommRing R] [Ring A]
    [Algebra R A] {x : A} {μ : R} (h : IsNilpotent (x - algebraMap R A μ)) (m : ℕ) :
    IsNilpotent (x ^ m - algebraMap R A (μ ^ m)) := by
  obtain ⟨q, hq⟩ := sub_dvd_pow_sub_pow (X : R[X]) (C μ) m
  have hx := congrArg (aeval x) hq
  simp only [map_mul, map_sub, map_pow, aeval_X, aeval_C] at hx
  have hc := (Commute.all (X - C μ) q).map (aeval x)
  simp only [map_sub, aeval_X, aeval_C] at hc
  rw [map_pow, hx]
  exact hc.isNilpotent_mul_right h

namespace LinearMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [IsAlgClosed K]

theorem charpoly_eq_prod_roots (f : V →ₗ[K] V) :
    f.charpoly = (f.charpoly.roots.map fun a ↦ X - C a).prod :=
  (IsAlgClosed.splits _).eq_prod_roots_of_monic f.charpoly_monic

theorem charpolyRev_eq_prod_roots (f : V →ₗ[K] V) :
    f.charpolyRev = (f.charpoly.roots.map fun a ↦ 1 - C a * X).prod := by
  rw [charpolyRev_def, ← reverse_multiset_prod_X_sub_C, ← charpoly_eq_prod_roots]

theorem card_roots_charpoly (f : V →ₗ[K] V) : f.charpoly.roots.card = finrank K V := by
  rw [(splits_iff_card_roots).mp (IsAlgClosed.splits _), charpoly_natDegree]

theorem det_eq_prod_roots_charpoly (f : V →ₗ[K] V) : f.det = f.charpoly.roots.prod := by
  classical
  set b := Module.finBasis K V with hb
  rw [← det_toMatrix b, ← charpoly_toMatrix f b, Matrix.det_eq_prod_roots_charpoly]

theorem zero_notMem_roots_charpoly {f : V →ₗ[K] V} (hf : IsUnit f.det) :
    (0 : K) ∉ f.charpoly.roots := fun h ↦ by
  rw [det_eq_prod_roots_charpoly, Multiset.prod_eq_zero h] at hf
  exact not_isUnit_zero hf

/-- Over an algebraically closed field, the trace of the `m`-th power of an endomorphism of a
finite-dimensional vector space is the `m`-th power sum of the roots of its characteristic
polynomial, counted with multiplicity. -/
theorem trace_pow_eq_sum_pow_roots_charpoly (f : Module.End K V) (m : ℕ) :
    LinearMap.trace K V (f ^ m) = (f.charpoly.roots.map (· ^ m)).sum := by
  classical
  have hindep : iSupIndep f.maxGenEigenspace := f.independent_maxGenEigenspace
  have hds : DirectSum.IsInternal f.maxGenEigenspace :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hindep
      (Module.End.iSup_maxGenEigenspace_eq_top f)
  have hfin : {μ : K | f.maxGenEigenspace μ ≠ ⊥}.Finite :=
    WellFoundedGT.finite_ne_bot_of_iSupIndep hindep
  have hmaps₁ : ∀ μ : K, MapsTo f ↑(f.maxGenEigenspace μ) ↑(f.maxGenEigenspace μ) :=
    fun μ ↦ f.mapsTo_maxGenEigenspace_of_comm rfl μ
  have hmaps : ∀ μ : K, MapsTo (f ^ m) ↑(f.maxGenEigenspace μ) ↑(f.maxGenEigenspace μ) :=
    fun μ ↦ f.mapsTo_maxGenEigenspace_of_comm ((Commute.refl f).pow_right m) μ
  have hterm : ∀ μ : K, LinearMap.trace K _ ((f ^ m).restrict (hmaps μ))
      = μ ^ m * (finrank K (f.maxGenEigenspace μ) : K) := by
    intro μ
    have h₁ : IsNilpotent
        (f.restrict (hmaps₁ μ) - algebraMap K (Module.End K (f.maxGenEigenspace μ)) μ) := by
      have h₀ := f.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap μ
      convert h₀ using 1
      ext x
      simp [Module.algebraMap_end_apply]
    have h₂ : (f ^ m).restrict (hmaps μ) = f.restrict (hmaps₁ μ) ^ m :=
      (Module.End.pow_restrict m (hmaps₁ μ)).symm
    rw [h₂]
    have := LinearMap.trace_comp_eq_mul_of_commute_of_isNilpotent (R := K)
      (M := f.maxGenEigenspace μ) (f := LinearMap.id)
      (g := f.restrict (hmaps₁ μ) ^ m) (μ ^ m) (Commute.one_left _)
      (isNilpotent_pow_sub_algebraMap_pow h₁ m)
    simpa using this
  rw [LinearMap.trace_eq_sum_trace_restrict' hds hfin hmaps]
  simp_rw [hterm]
  rw [Finset.sum_multiset_map_count]
  refine Finset.sum_congr ?_ fun μ _ ↦ ?_
  · ext μ
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Multiset.mem_toFinset,
      ← Multiset.count_ne_zero, count_roots, ← LinearMap.finrank_maxGenEigenspace_eq, ne_eq,
      Submodule.finrank_eq_zero]
  · rw [count_roots, ← LinearMap.finrank_maxGenEigenspace_eq, nsmul_eq_mul, mul_comm]

/-- Over an algebraically closed field the traces of the powers of an endomorphism depend only
on its characteristic polynomial. -/
theorem trace_pow_eq_of_charpoly_eq {W : Type*} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] {f : Module.End K V} {g : Module.End K W}
    (h : f.charpoly = g.charpoly) (k : ℕ) :
    LinearMap.trace K V (f ^ k) = LinearMap.trace K W (g ^ k) := by
  rw [trace_pow_eq_sum_pow_roots_charpoly, trace_pow_eq_sum_pow_roots_charpoly, h]

end LinearMap

variable {K : Type*} [Field K] [IsAlgClosed K] {n : Type*} [Fintype n] [DecidableEq n]

/-- Over an algebraically closed field, the trace of the `m`-th power of a matrix is the `m`-th
power sum of the roots of its characteristic polynomial, counted with multiplicity. -/
theorem Matrix.trace_pow_eq_sum_pow_roots_charpoly (A : Matrix n n K) (m : ℕ) :
    (A ^ m).trace = (A.charpoly.roots.map (· ^ m)).sum := by
  rw [← Matrix.charpoly_toLin' A, ← LinearMap.trace_pow_eq_sum_pow_roots_charpoly A.toLin' m,
    ← Matrix.toLin'_pow, Matrix.trace_toLin'_eq]

/-- Over an algebraically closed field, the reciprocal characteristic polynomial
`det (1 - t • A)` of a matrix is the product of `1 - μ t` over the roots `μ` of its
characteristic polynomial, counted with multiplicity. -/
theorem Matrix.charpolyRev_eq_prod_one_sub_smul (A : Matrix n n K) :
    A.charpolyRev = (A.charpoly.roots.map fun l ↦ 1 - C l * X).prod := by
  rw [← reverse_multiset_prod_X_sub_C,
    ← (IsAlgClosed.splits A.charpoly).eq_prod_roots_of_monic A.charpoly_monic, A.reverse_charpoly]

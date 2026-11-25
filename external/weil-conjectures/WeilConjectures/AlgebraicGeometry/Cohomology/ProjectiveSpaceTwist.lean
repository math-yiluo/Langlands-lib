/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.ProjectiveFinite

/-!
# The cohomology of the twisting sheaves on `ℙⁿ_A` over a commutative ring

Let `A` be a commutative ring and `ℙᵈ_A = ℙ(n; Spec A)` with `Fintype.card n = d + 1`. This file
packages the sheaf-level statements of `lem-pc-projective-space-twist-cohomology` over `A`, as
`A`-modules (through `Scheme.Modules.moduleHOfSpec`), by composing Leray's theorem for the
standard affine covering with the computation of the monomial Čech complex:

* `H⁰(ℙᵈ_A, 𝒪(D)) ≅ A[x₀, …, x_d]_D` for `D ≥ 0`, and `H⁰(ℙᵈ_A, 𝒪(m)) = 0` for `m < 0`, `d ≥ 1`;
* `H^q(ℙᵈ_A, 𝒪(m)) = 0` for `q ∉ {0, d}`;
* `Hᵈ(ℙᵈ_A, 𝒪(m))` is free on the strictly negative exponent vectors of sum `m`; it vanishes
  for `m ≥ -d` (`d ≥ 1`), `Hᵈ(ℙᵈ_A, 𝒪(-d-1)) ≅ A`, and `Hᵈ(ℙᵈ_A, 𝒪(m)) ≅ (A[xᵢ]_{-m-d-1})^∨`
  for `m ≤ -d - 1`;
* for `d = 0`, `H⁰(ℙ⁰_A, 𝒪(m)) ≅ A` for every `m`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry.ProjectiveSpace

open Scheme.Modules

variable {n : Type u}

/-- **`H⁰` of the twisting sheaves over a ring**: `H⁰(ℙⁿ_A, 𝒪(D)) ≅ A[x₀, …, xₙ]_D` for `D ≥ 0`,
as `A`-modules, for any commutative ring `A`.

(blueprint: `lem-pc-projective-space-twist-cohomology` (i)) -/
theorem nonempty_H_zero_twist_linearEquiv (A : Type u) [CommRing A] [Finite n] [Nonempty n]
    (D : ℕ) :
    letI := moduleHOfSpec (ℙ(n; Spec (.of A)) ↘ Spec (.of A)) (twist n (Spec (.of A)) D) 0
    Nonempty ((twist n (Spec (.of A)) D).H 0 ≃ₗ[A] MvPolynomial.homogeneousSubmodule n A D) := by
  let := moduleHOfSpec (ℙ(n; Spec (.of A)) ↘ Spec (.of A)) (twist n (Spec (.of A)) D) 0
  have := Fintype.ofFinite n
  obtain ⟨e⟩ := nonempty_H_twist_linearEquiv_monomialCechComplex_homology (n := n) A D 0
  exact ⟨e ≪≫ₗ monomialCechComplexHomologyZeroLinearEquiv n A D⟩

/-- **Vanishing in the middle degrees over a ring**: `H^q(ℙᵈ_A, 𝒪(m)) = 0` for `q ∉ {0, d}`.

(blueprint: `lem-pc-projective-space-twist-cohomology`) -/
theorem subsingleton_H_twist_of_ne_of_commRing (A : Type u) [CommRing A] [Fintype n] {d : ℕ}
    (hn : Fintype.card n = d + 1) (m : ℤ) {q : ℕ} (hq0 : q ≠ 0) (hqd : q ≠ d) :
    Subsingleton ((twist n (Spec (.of A)) m).H q) := by
  rcases lt_or_gt_of_ne hqd with hlt | hlt
  · exact subsingleton_H_twist_of_pos_of_lt A hn m (Nat.pos_of_ne_zero hq0) hlt
  · exact subsingleton_H_of_lt n A (by rwa [Nat.card_eq_fintype_card]) _ hlt

/-- **The top cohomology of the twisting sheaves over a ring**: `Hᵈ(ℙᵈ_A, 𝒪(m))` is the free
`A`-module on the strictly negative exponent vectors `e` of sum `m`, the basis vector `e` being
the class of the Čech cocycle `xᵉ` on `U₀ ∩ ⋯ ∩ U_d` (for `d = 0` this requires `m < 0`).

(blueprint: `lem-pc-projective-space-twist-cohomology` (ii)) -/
theorem nonempty_H_twist_top_linearEquiv_finsupp (A : Type u) [CommRing A] [Fintype n] {d : ℕ}
    (hn : Fintype.card n = d + 1) {m : ℤ} (hm : d ≠ 0 ∨ m < 0) :
    letI := moduleHOfSpec (ℙ(n; Spec (.of A)) ↘ Spec (.of A)) (twist n (Spec (.of A)) m) d
    Nonempty ((twist n (Spec (.of A)) m).H d ≃ₗ[A] (negativeExponents n m →₀ A)) := by
  let := moduleHOfSpec (ℙ(n; Spec (.of A)) ↘ Spec (.of A)) (twist n (Spec (.of A)) m) d
  obtain ⟨e⟩ := nonempty_H_twist_linearEquiv_monomialCechComplex_homology (n := n) A m d
  exact ⟨e ≪≫ₗ monomialCechComplexHomologyTopLinearEquiv n A m hn
    (Fintype.equivFinOfCardEq hn).symm hm⟩

/-- **Vanishing of the top cohomology over a ring**: `Hᵈ(ℙᵈ_A, 𝒪(m)) = 0` for `m ≥ -d`, `d ≥ 1`.

(blueprint: `lem-pc-projective-space-twist-cohomology` (ii)) -/
theorem subsingleton_H_twist_top_of_commRing (A : Type u) [CommRing A] [Fintype n] {d : ℕ}
    (hn : Fintype.card n = d + 1) (hd : d ≠ 0) {m : ℤ} (hm : -(d : ℤ) ≤ m) :
    Subsingleton ((twist n (Spec (.of A)) m).H d) := by
  obtain ⟨e⟩ := nonempty_H_twist_linearEquiv_monomialCechComplex_homology (n := n) A m d
  have := subsingleton_monomialCechComplex_homology_top (A := A) hn hd hm
  exact e.toEquiv.subsingleton

/-- **`Hᵈ(ℙᵈ_A, 𝒪(-d-1)) ≅ A`** for `d ≥ 1`: the top cohomology of `𝒪(-d-1)` is free of rank
one, with basis the class of `x₀⁻¹ ⋯ x_d⁻¹`.

(blueprint: `lem-pc-projective-space-twist-cohomology` (ii)) -/
theorem nonempty_H_twist_top_linearEquiv_self (A : Type u) [CommRing A] [Fintype n] {d : ℕ}
    (hn : Fintype.card n = d + 1) (hd : d ≠ 0) :
    letI := moduleHOfSpec (ℙ(n; Spec (.of A)) ↘ Spec (.of A))
      (twist n (Spec (.of A)) (-(d : ℤ) - 1)) d
    Nonempty ((twist n (Spec (.of A)) (-(d : ℤ) - 1)).H d ≃ₗ[A] A) := by
  let := moduleHOfSpec (ℙ(n; Spec (.of A)) ↘ Spec (.of A))
    (twist n (Spec (.of A)) (-(d : ℤ) - 1)) d
  have : Subsingleton (negativeExponents n (-(d : ℤ) - 1)) :=
    ⟨fun e e' ↦ (eq_negOneExponents hn e).trans (eq_negOneExponents hn e').symm⟩
  obtain ⟨e⟩ := nonempty_H_twist_top_linearEquiv_finsupp (n := n) A hn (m := -(d : ℤ) - 1)
    (.inl hd)
  exact ⟨e ≪≫ₗ Finsupp.uniqueLinearEquiv A A (negOneExponents n hn)⟩

/-- **The top cohomology of the twisting sheaves as a dual, over a ring**:
`Hᵈ(ℙᵈ_A, 𝒪(m)) ≅ (A[xᵢ]_{-m-d-1})^∨` for `m ≤ -d - 1`.

(blueprint: `lem-pc-projective-space-twist-cohomology` (ii),
`theorem-riemann-roch-coherent-serre-duality--2`) -/
theorem nonempty_H_twist_top_linearEquiv_dual (A : Type u) [CommRing A] [Fintype n] {d : ℕ}
    (hn : Fintype.card n = d + 1) {m : ℤ} (hm : m ≤ -(d : ℤ) - 1) :
    letI := moduleHOfSpec (ℙ(n; Spec (.of A)) ↘ Spec (.of A)) (twist n (Spec (.of A)) m) d
    Nonempty ((twist n (Spec (.of A)) m).H d ≃ₗ[A]
      Module.Dual A (MvPolynomial.homogeneousSubmodule n A (-m - d - 1).toNat)) := by
  let := moduleHOfSpec (ℙ(n; Spec (.of A)) ↘ Spec (.of A)) (twist n (Spec (.of A)) m) d
  obtain ⟨e⟩ := nonempty_H_twist_linearEquiv_monomialCechComplex_homology (n := n) A m d
  exact ⟨e ≪≫ₗ monomialCechComplexHomologyTopLinearEquivDual n A m hn hm⟩

/-- With a single coordinate, the strictly negative exponent vectors of sum `m < 0` form a
singleton. -/
lemma nonempty_unique_negativeExponents [Fintype n] (hn : Fintype.card n = 1) {m : ℤ}
    (hm : m < 0) : Nonempty (Unique (negativeExponents n m)) := by
  obtain ⟨i, hi⟩ := Fintype.card_eq_one_iff.1 hn
  have hsum (e : n → ℤ) : ∑ j, e j = e i := by
    rw [Fintype.sum_eq_single i fun j hj ↦ (hj (hi j)).elim]
  refine ⟨{ default := ⟨fun _ ↦ m, by rw [hsum], fun _ ↦ hm⟩, uniq := fun e ↦ ?_ }⟩
  obtain ⟨e, hs, -⟩ := e
  refine Subtype.ext (funext fun j ↦ ?_)
  rw [hsum] at hs
  rw [hi j]
  exact hs

/-- With a single coordinate, the monomials of degree `D` form a singleton. -/
lemma nonempty_unique_degree_eq [Fintype n] (hn : Fintype.card n = 1) (D : ℕ) :
    Nonempty (Unique {s : n →₀ ℕ | s.degree = D}) := by
  obtain ⟨i, hi⟩ := Fintype.card_eq_one_iff.1 hn
  refine ⟨{ default := ⟨Finsupp.single i D, by simp⟩, uniq := fun s ↦ ?_ }⟩
  obtain ⟨s, hs⟩ := s
  refine Subtype.ext (Finsupp.ext fun j ↦ ?_)
  change Finsupp.degree s = D at hs
  rw [Finsupp.degree_eq_sum, Fintype.sum_eq_single i fun j hj ↦ (hj (hi j)).elim] at hs
  rw [hi j]
  simp [hs]

/-- **The case `n = 0`**: on `ℙ⁰_A = Spec A`, `H⁰(𝒪(m)) ≅ A` for every `m`; the higher
cohomology vanishes by `subsingleton_H_of_lt`.

(blueprint: `lem-pc-projective-space-twist-cohomology`) -/
theorem nonempty_H_zero_twist_linearEquiv_of_card_eq_one (A : Type u) [CommRing A] [Fintype n]
    (hn : Fintype.card n = 1) (m : ℤ) :
    letI := moduleHOfSpec (ℙ(n; Spec (.of A)) ↘ Spec (.of A)) (twist n (Spec (.of A)) m) 0
    Nonempty ((twist n (Spec (.of A)) m).H 0 ≃ₗ[A] A) := by
  let := moduleHOfSpec (ℙ(n; Spec (.of A)) ↘ Spec (.of A)) (twist n (Spec (.of A)) m) 0
  have : Nonempty n := Fintype.card_pos_iff.1 (by omega)
  rcases lt_or_ge m 0 with hm | hm
  · obtain ⟨_⟩ := nonempty_unique_negativeExponents hn hm
    obtain ⟨e⟩ := nonempty_H_twist_top_linearEquiv_finsupp (n := n) A (d := 0) hn (.inr hm)
    exact ⟨e ≪≫ₗ Finsupp.uniqueLinearEquiv A A default⟩
  · obtain ⟨D, rfl⟩ := Int.eq_ofNat_of_zero_le hm
    obtain ⟨_⟩ := nonempty_unique_degree_eq hn D
    obtain ⟨e⟩ := nonempty_H_zero_twist_linearEquiv (n := n) A D
    exact ⟨e ≪≫ₗ (homogeneousSubmoduleBasis n A D).repr ≪≫ₗ
      Finsupp.uniqueLinearEquiv A A default⟩

end AlgebraicGeometry.ProjectiveSpace

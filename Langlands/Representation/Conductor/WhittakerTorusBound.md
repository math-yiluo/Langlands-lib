# Exponential bounds for Whittaker coefficients on the dominant torus

Author: Worker 5220. Internal helper module for the proof of
`Langlands.Conductor.SphericalCorankOneConvergenceStatement`; it introduces no
statement.

## Setting

`F` is a nonarchimedean local field (any characteristic), `π` a complex
representation of `GL_(m+1)(F)`, `ψ` a unitary additive character trivial on the
integers, `ℓ : glFunctionals ψ m π` a standard Whittaker functional, `ϖ` with
valuation at most one, and `K = principalLevelOpenSubgroup F m a` the principal
congruence subgroup of positive level `a`. For `μ : Fin (m + 1) → ℤ`,
`torus ϖ μ = diag(ϖ^μ_0, …, ϖ^μ_m)`.

## Results

- `principalLevel_borel_factor`: every `k ∈ K` is `l * d * u` with `l` lower
  unipotent, `d` diagonal, `u` upper unipotent, all in `K` (the published
  `BlockShape.principalLevelSubgroup_iwahoriProduct_surjective` for the singleton
  block shape). `borelUpper`, `borelLevi`, `borelLower` abbreviate the three
  subgroups.
- `torus_upper_conj_mem`, `torus_lower_conj_mem`, `torus_levi_conj_mem`: for
  antitone `μ`, `ϖ^μ (K ∩ N) ϖ^(-μ) ⊆ K`, `ϖ^(-μ) (K ∩ N̄) ϖ^μ ⊆ K`, and conjugation
  fixes `K ∩ M` (from `principal_upper_conj`, `principal_lower_inv_conj`,
  `ratio_mem_integer`).
- `compressedAction_torus_add`: for antitone `μ, ν` the compressed action
  `e_K π(·)` on `K`-fixed vectors satisfies
  `e_K π(ϖ^(μ+ν)) = e_K π(ϖ^μ) ∘ e_K π(ϖ^ν)` (the published
  `Jacquet.compressedAction_mul_of_factor`).
- `whittaker_compressedAction_torus`: for antitone `μ` and `K`-fixed `v`,
  `ℓ (e_K π(ϖ^μ) v) = ℓ (π(ϖ^μ) v)`. Each `K`-translate of `π(ϖ^μ) v` is a
  `K ∩ N`-translate (`Jacquet.exists_upper_translate`), and `ψ` is trivial on
  integral upper unipotent matrices (`isIntegrallyTrivial_standardCharacter`).
- Lattice combinatorics: `dominantGenerator` (indicators of initial segments and
  the constant `-1`), `latticeExponent`, `exponentGap`, `dominantCoordinates`.
  `latticeExponent_dominantCoordinates` writes every antitone `μ` as a
  nonnegative combination of the generators (telescoping, `sum_exponentGap`), and
  `sum_dominantCoordinates_le` bounds the total coefficient by
  `(2m+4) ∑ |μ_j|`.
- `whittaker_torus_bound`: if `π` is admissible, there is `A ≥ 1` such that every
  `K`-fixed `v` has a `C > 0` with `‖ℓ (π(ϖ^μ) v)‖ ≤ C A^(∑ |μ_j|)` for all
  antitone `μ`. The compressions of the generators act on the finite-dimensional
  space of `K`-fixed vectors and are multiplicative, so the published
  `UnrestrictedLatticeBound.exists_apply_le_prod` gives a product bound, which
  the two previous facts turn into the stated bound.
- `whittaker_torus_bound_finite`: the same bound uniformly on a finite set of
  `K`-fixed vectors.

## Provenance

This is the standard exponential growth estimate for Whittaker functions on the
dominant cone used in JPSS 1983 (H. Jacquet, I. I. Piatetski-Shapiro, J. A.
Shalika, *Rankin–Selberg convolutions*, Amer. J. Math. 105 (1983), §2) to prove
absolute convergence. The proof here is the elementary compression argument
(Jacquet's lemma for the Borel subgroup), not the asymptotic expansion.

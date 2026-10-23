# Elementary facts on norms of number field elements

This module proves three elementary facts for the approximation step of the Artin–Tate norm
argument in the reciprocity proof (task fb66219f):

- the field norm `N_{K/ℚ}(t + α)` is positive for every large rational `t`;
- the norm of an algebraic integer `≡ 1 mod n` is `≡ 1 mod n`;
- a rational integer `≡ 1` modulo a high enough power of `ℓ` has trivial cyclotomic symbol
  at `ℓ`.

Everything is in the namespace `Langlands.Global.CyclotomicSymbol`. `K` is a number field.

## Positivity

- `norm_algebraMap_add t α`: `N_{K/ℚ}(t + α)` equals the characteristic polynomial of
  multiplication by `-α` on the `ℚ`-vector space `K`, evaluated at `t`. The proof uses
  Mathlib's `LinearMap.eval_charpoly`, which says `f.charpoly.eval t = det(t − f)`, together
  with `Algebra.norm_apply`, which says `N(x) = det(lmul x)`.
- `eventually_norm_algebraMap_add_pos α`: `0 < N_{K/ℚ}(t + α)` for all sufficiently large
  `t ∈ ℚ`. The characteristic polynomial is monic of degree `[K : ℚ] > 0`, so it tends to
  `+∞` (`Polynomial.tendsto_atTop_of_leadingCoeff_nonneg`).
- `exists_norm_add_nsmul_pos α (hT : 0 < T)`: some `k ∈ ℕ` has
  `0 < N_{K/ℚ}(α + kT)`.

The approximation argument needs a global element `α` close to prescribed local values,
with positive norm. Adding a large multiple of an integer `T` divisible by high powers of
the relevant primes gives positivity without changing the local approximations. This
replaces the positivity at the real places used by Artin–Tate.

## Congruence

- `intNorm_sub_one_dvd n α β`: if `α = 1 + n β` in `𝓞 K`, then `n` divides
  `N_{𝓞K/ℤ}(α) − 1`. With an integral basis, `N(α)` is the determinant of the matrix of
  multiplication by `α` (`Algebra.norm_eq_matrix_det`). Modulo `n` that matrix is the identity
  matrix (`RingHom.map_det`). Mathlib's `Algebra.coe_norm_int` identifies `N_{𝓞K/ℤ}` with
  `N_{K/ℚ}` on integers.

## The symbol of an integer near `1`

- `ratLocalSymbol_intCast_eq_one m ℓ z`: let `ℓ^r` be the `ℓ`-part of `m`. If `z ∈ ℤ`,
  `z ≠ 0`, and `ℓ^{r+1}` divides `z − 1`, then `ratLocalSymbol m ℓ z = 1`. Indeed,
  `‖z − 1‖_ℓ ≤ ℓ^{-(r+1)}` (`Padic.norm_int_le_pow_iff_dvd`). This bound is at most `ℓ^{-r}`
  and below `1`, so the local constancy result `localSymbol_eq_one` applies.

## Provenance

These are standard facts. They stand in for steps of Artin–Tate's proof of their
Theorem 2 in Chapter VII §2 (printed p.39, PDF p.48): weak approximation, and the continuity
of `α_p ↦ σ_p(α_p)`. The polynomial positivity argument is an internal choice. It avoids
approximation at the infinite places.

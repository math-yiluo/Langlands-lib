# Analytic comparisons over a normed field

This module proves two analytic lemmas used in `Langlands.Algebra.DegreeDeterminant.DegreeData.det_eq`. It defines nothing.

## Order of vanishing from norms

`rootMultiplicity_zero_eq_of_norm_eval_eq`: let `K` be a nontrivially normed field and `u, v : K[X]` with `v ≠ 0`. Suppose that `‖u.eval t‖ = ‖v.eval t‖` for every `t` with `‖t‖ ≤ 1` and `v.eval t ≠ 0`. Then `u` and `v` have the same order of vanishing at `0` (`rootMultiplicity 0`).

Proof. Choose `c` with `0 < ‖c‖ < 1` and set `t_N = c ^ N`. Then `t_N → 0`, `t_N ≠ 0` and `N ↦ t_N` is injective, so `v.eval t_N ≠ 0` for all large `N` (`v` has finitely many roots). This forces `u ≠ 0`. Write `u = X ^ a · u₁` and `v = X ^ b · v₁` with `u₁(0) ≠ 0` and `v₁(0) ≠ 0` (Mathlib's `exists_eq_pow_rootMultiplicity_mul_and_not_dvd`). For large `N`, `‖t_N‖ ^ a ‖u₁(t_N)‖ = ‖t_N‖ ^ b ‖v₁(t_N)‖`. The helper `not_lt_of_norm_eq` shows that `a < b` is impossible: otherwise `‖u₁(t_N)‖ = ‖t_N‖ ^ (b - a) ‖v₁(t_N)‖ → 0`, while `‖u₁(t_N)‖ → ‖u₁(0)‖ ≠ 0`. By symmetry `b < a` is impossible too.

## Density of natural-number points in `ℤ_[p] ^ n`

`norm_eval_eq_of_natCast`: let `P, E` be multivariate polynomials over `ℚ_[p]` in `n` variables. Suppose that `‖P(x)‖ = ‖E(x)‖` at every natural-number point `x` with `E(x) ≠ 0`. Then `‖P(y)‖ = ‖E(y)‖` at every `y` with all `‖y_i‖ ≤ 1` and `E(y) ≠ 0`.

Proof. On `ℤ_[p] ^ n` both sides are continuous (`MvPolynomial.continuous_eval`). The set `U` where `E` does not vanish is open. The natural-number points are dense (Mathlib's `PadicInt.denseRange_natCast` and `DenseRange.piMap`). So `U` lies in the closure of its intersection with the natural-number points (`Dense.open_subset_closure_inter`). The two continuous functions agree there, hence on `U` (`Set.EqOn.closure`).

## Provenance

Both lemmas carry out the analytic part of Milne's Lemma 12.10 (*Abelian Varieties*, author revision 2022, p. 23), which Milne cites from Lang. The arguments here are standard and internal; they are not copied from a source.

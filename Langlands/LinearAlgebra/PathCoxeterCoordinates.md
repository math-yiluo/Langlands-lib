# Coordinates of path Coxeter products with a pattern block

This module is pure algebra over an arbitrary commutative ring `R`, in the namespace
`Langlands.LinearAlgebra.PathCoxeter`. It imports `Langlands.LinearAlgebra.PathCoxeterCharpoly`
and continues it. That module computes two kinds of characteristic polynomials on `2 k + 3`
lines: those of ordinary path products (`charpoly_pprod`) and those of path products with a
pattern block in the middle (`charpoly_pathMat_pattern`). This module shows that every pattern
characteristic polynomial is an ordinary one, with explicit "ordinary coordinates" `patCoord`.
It also shows that the coordinate map `(d, σ, δ) ↦ patCoord k d σ δ` is injective on the
relevant parameters and surjective.

The module is an internal prerequisite of the split even-path cross-section task
(`Langlands.GroupScheme.SplitEvenChainCrossSectionStatement`, Steinberg 1965, §9.15–9.19).
There, the characteristic polynomial of a path representation identifies a pattern element with
an ordinary Steinberg product.

**Provenance: internal.** The module has no counterpart in the literature. Steinberg's §9 proves
the cross-section by other means, and these formulas were derived for this project. Every result
is stated in full below and proved in Lean.

## Definitions

Sequences are functions `ℕ → R`. Only finitely many of their values matter.

- `ordPoly k γ = X^(2k+3) + Σ_{j<2k+2} (-1)^j γ_j X^(2k+2-j) - 1`. This is the characteristic
  polynomial of the ordinary path product with coordinates `γ`
  (`charpoly_pprod_eq_ordPoly`, which restates `charpoly_pprod`).
- `qPoly k u = -Σ_{j<2k+3} (-1)^j u_j X^(2k+2-j)`.
- `patU k d σ`: the sequence whose value at `j` is
  - `-1` for `j = 0`;
  - `d (j-1)` for `1 ≤ j ≤ k`;
  - `σ` for `j = k + 1`;
  - `d j` for `k + 2 ≤ j ≤ 2k + 1`;
  - `-1` for `j ≥ 2k + 2`.
- `patCoord k d σ δ j = patU k d σ j + patU k d σ (j+1) + (δ if j = k + 1, else 0)`. These are the
  ordinary coordinates of a pattern product.
- `solveU k γ δ`: the sequence with `u_0 = -1` and `u_(j+1) = γ_j - u_j - (δ if j = k + 1,
  else 0)`. It is used in the surjectivity proof.

## Results

- `coeff_neg_one_pow_mul_C_mul_X_pow`: the coefficient of `X^m` in `(-1)^j C r X^n` is
  `(-1)^j r` if `m = n`, and `0` otherwise.
- `ordPoly_coeff`: for `j < 2k+2`, the coefficient of `X^(2k+2-j)` in `ordPoly k γ` is
  `(-1)^j γ_j`.
- `eq_of_ordPoly_eq`: if `ordPoly k γ = ordPoly k γ'`, then `γ_j = γ'_j` for all `j < 2k+2`.
- `ordPoly_shift`: let `u_0 = u_(2k+2) = -1`. Then the ordinary polynomial with coordinates
  `u_j + u_(j+1) + (δ if j = k + 1, else 0)` equals `(X - 1) qPoly k u + (-1)^(k+1) δ X^(k+1)`.
- `patU_succ_of_lt` (`i < k`): `patU k d σ (i+1) = d i`. `patU_right` (`i < k`):
  `patU k d σ (k+2+i) = d (k+2+i)`.
- `qPoly_patU`: `qPoly k (patU k d σ)` equals

  `X^(2k+2) + Σ_{i<k} (-1)^i d_i X^(2k+1-i) + (-1)^(k+1) (-σ) X^(k+1)`
  `+ Σ_{i<k} (-1)^(k+1+i) d_(k+2+i) X^(k-i) + 1`.

- `ordPoly_patCoord`: `ordPoly k (patCoord k d σ δ) = (X - 1) qPoly k (patU k d σ) +
  (-1)^(k+1) δ X^(k+1)`.
- **`charpoly_pathMat_pattern_eq_ordPoly`.** Take the hypotheses of `charpoly_pathMat_pattern`:
  `β 1 2 = β 2 2 = 0`, `β 1 1 = 1`, `β 2 1 = 0` and `β 0 2 β 2 0 = -1`. Then
  `charpoly (pathMat k c β) = ordPoly k (patCoord k c (-β 0 0) (β 0 1 * β 1 0))`.
- `sum_alternating_add_succ`: `Σ_{j<N} (-1)^j (u_j + u_(j+1)) = u_0 - (-1)^N u_N`.
- `sum_alternating_patCoord`: `Σ_{j<2k+2} (-1)^j patCoord k d σ δ j = (-1)^(k+1) δ`.
- **`eq_of_patCoord_eq`** (injectivity). Suppose `patCoord k d σ δ j = patCoord k d' σ' δ' j`
  for all `j < 2k+2`. Then `δ = δ'` and `σ = σ'`. Moreover `d i = d' i` and
  `d (k+2+i) = d' (k+2+i)` for all `i < k`. The values `d k` and `d (k+1)` do not enter.
- **`exists_patCoord_eq`** (surjectivity). For every `γ : ℕ → R` there are `d` and `σ` such that
  `patCoord k d σ δ j = γ j` for all `j < 2k+2`, where
  `δ = (-1)^(k+1) Σ_{i<2k+2} (-1)^i γ_i`.

## Proof as implemented

**Coefficients.** `ordPoly_coeff` expands the coefficient of the sum with `finsetSum_coeff` and
keeps the single term `j` (`Finset.sum_eq_single`). The other terms and the two outer monomials
vanish by `omega` on the exponents. `eq_of_ordPoly_eq` multiplies the resulting equation by
`(-1)^j` and uses `(-1)^(2j) = 1`.

**`ordPoly_shift`.** Write `S0` and `S1` for the sums of `(-1)^j u_j X^(2k+2-j)` and of
`(-1)^j u_(j+1) X^(2k+2-j)` over `j < 2k+2`. The coordinate sum splits as `S0 + S1` plus the
single `δ` term. Peeling off the last term gives `Σ_{j<2k+3} (-1)^j u_j X^(2k+2-j) = S0 - 1`,
because `u_(2k+2) = -1`. Peeling off the first term (`Finset.sum_range_succ'`) and multiplying
by `X` gives `-X^(2k+3) - S1`, because `u_0 = -1`. The identity then follows by `ring`.

**`qPoly_patU`.** Split `range (2k+3)` as `range (k+2) ++ (k+2 + range (k+1))`. Then peel off
the terms `0`, `k+1` and `2k+2`, and evaluate `patU` termwise with `patU_succ_of_lt` and
`patU_right`. The parities are simplified with `(-1)^(2k+2) = 1`, and `ring` finishes.

**`ordPoly_patCoord`** is `ordPoly_shift` with `u = patU k d σ`.
**`charpoly_pathMat_pattern_eq_ordPoly`** rewrites `charpoly_pathMat_pattern` with
`ordPoly_patCoord` and `qPoly_patU`, and finishes with `ring`.

**Injectivity.** `sum_alternating_add_succ` is a telescoping induction on `N`. It gives
`sum_alternating_patCoord`, because `patU` is `-1` at `0` and at `2k+2`. So the alternating sum
of the coordinates determines `δ`. With `δ` fixed, induction on `j` shows that the sequences
`patU k d σ` and `patU k d' σ'` agree for `j ≤ 2k+2`: each coordinate equation determines
`u_(j+1)` from `u_j` (`linear_combination`). Evaluating at `k+1`, `i+1` and `k+2+i` gives the
claims.

**Surjectivity.** Let `u = solveU k γ δ`. By construction,
`u_j + u_(j+1) + (δ if j = k + 1, else 0) = γ_j` for every `j`. The telescoping sum and the
choice of `δ` give `u_(2k+2) = -1`. Take `d i = u (i+1)` for `i < k`, `d i = u i` otherwise,
and `σ = u (k+1)`. Then `patU k d σ` agrees with `u` on `j ≤ 2k+2`, which gives the claim.

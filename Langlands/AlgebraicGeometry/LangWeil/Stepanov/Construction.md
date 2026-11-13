# The linear algebra of the Stepanov construction

Author: Worker 5406. Internal helper for the proof of
`Langlands.AlgebraicGeometry.LangWeil.StepanovNormPolynomialsStatement`.

Provenance. Schmidt, *Zur Methode von Stepanov* (Acta Arith. 24, 1973), constructs auxiliary
polynomials `A = ∑_{j,k} B_{jk}(X, Y) X^{qj} Y^{qk}` with unknown coefficients and imposes linear
conditions so that `A` vanishes to high order along the curve; Hilfssatz 3 (printed p.350)
guarantees that the resulting `A` is not divisible by `f`. This module sets up the unknowns, the
linear conditions (in our branch formulation, see `Branch.md`, `PointBranch.md`) and the
resultant `Res_Y(P, A)`. The exact choice of conditions of the second kind (for points moved by
Frobenius) is our own variant.

Notation: `R2 = F[X][Y]`, `P ∈ R2` with `n = natDegree P` (degree in `Y`), leading coefficient
`g₀ = P.leadingCoeff ∈ F[X]`.

## Definitions

- `Idx N n d = Fin (N + 1) × Fin n × Fin n × Fin (d + 1)`: index `(j, k, i, e)` of the unknown
  coefficient of `X^e Y^i` in `B_{jk}`.
- `coefPolyL N n d j k : (Idx N n d → F) →ₗ[F] R2`,
  `B_{jk}(v) = ∑_{i < n, e ≤ d} v(j, k, i, e) X^e Y^i` (zero unless `j ≤ N`, `k < n`).
- `Ql P l : R2 →ₗ[F] R2`, `Q_l B = coeff_l (sigma P B)` (coefficient of `S^l` of the universal
  branch substitution of `Branch.lean`).
- First kind: `E1L P N n d l v = ∑_{j ≤ N, k < n} Q_l(B_{jk}(v)) X^j Y^k`.
- `eL P N n d l k v = ∑_{j ≤ N} Q_l(B_{jk}(v)) X^j`.
- Second kind: `E2L P N n d l k v = g₀ · e_{l,k} - e_{l,n-1} · ε_k` with `ε_k = divX^[k+1] P`.
- `normPoly q N n d v = ∑_{j ≤ N, k < n} B_{jk}(v) X^{qj} Y^{qk}`.

## Results

- `smul_eq_CC_mul`, `coeff_divX_iterate`, `inBox_divX_iterate`, `divX_iterate_natDegree`
  (`divX^[n] P = C g₀`), `divX_iterate_map`.
- `inBox_coefPolyL` (box `(d, n - 1)`), `coeff_coeff_coefPolyL` (the coefficients of `B_{jk}(v)`
  are the `v(j, k, i, e)`), `exists_coefPolyL_ne_zero` (`v ≠ 0` gives some `B_{jk}(v) ≠ 0`).
- `inBox_Ql`, `inBox_Ql_coefPolyL`: `Q_l(B_{jk})` lies in box
  `(d + l(2m - 1), (n - 1) + l(2n - 2))` when `P` lies in box `(m, n)` (from `inW_sigma`).
- `inBox_E1L`: `E1_l` lies in box `(d + l(2m - 1) + N, (n - 1)(2l + 2))`;
  `inBox_eL`; `inBox_E2L`: `E2_{l,k}` lies in box `(d + l(2m - 1) + N + m, (n - 1)(2l + 2))`.
- `inBox_normPoly`: `A(v)` lies in box `(d + qN, (n - 1)(q + 1))`;
  `normPoly_eq_sum_mul_pow` rewrites `A(v)` as `∑ B_{jk}(v) (X^j Y^k)^q`.
- `normPoly_resultant`: let `F` be finite with `q` elements, `P` absolutely irreducible
  (irreducible over `AlgebraicClosure F`), `1 ≤ n`, all coefficients of `P` of degree `≤ m`,
  `n d + m (n - 1)² < q`, and assume `Res_Y(P, A) ≠ 0` whenever `natDegree A ≤ D` and
  `¬ P ∣ A` (hypothesis `hres`, discharged later by `resultant_ne_zero_of_not_dvd` of
  `RootTools.lean`). Then for `v ≠ 0`, `h = Res_Y(P, A(v))` with sizes `n` and
  `D = (n - 1)(q + 1)` is nonzero, has `natDegree h ≤ (n - 1)(q + 1) m + n (d + qN)`, and
  `natDegree A(v) ≤ D`. Non-divisibility `¬ P ∣ A(v)` is exactly Schmidt's Hilfssatz 3,
  `frobeniusIndependence` (`FrobeniusIndependence.lean`); the degree bound is
  `resultant_natDegree_le` (`ResultantDegree.lean`).

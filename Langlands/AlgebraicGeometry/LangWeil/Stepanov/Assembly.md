# The two auxiliary norm polynomials

Author: Worker 5406. Internal helper for the proof of
`Langlands.AlgebraicGeometry.LangWeil.StepanovNormPolynomialsStatement`.

Provenance. This is the core of Stepanov's method as presented by Schmidt, *Zur Methode von
Stepanov* (Acta Arith. 24, 1973): one auxiliary polynomial vanishes to high order at the
rational points of the curve, the other at the geometric points that are not rational. Our
formulation (branches instead of hyperderivatives; conditions of the second kind built from
`divX` iterates of `P`) is an own variant; it produces the polynomials `h₁, h₂` required by the
Library statement `StepanovNormPolynomialsStatement`.

Notation: `F` finite with `q = Nat.card F` elements, `P ∈ F[X][Y]` with `n = natDegree P ≥ 1`,
coefficients of degree `≤ m`, `ev`, `rho`, `normPoly`, `E1L`, `E2L` as in `PointBranch.lean` and
`Construction.lean`.

## Results

- `exists_charP_card`: `q = p^k` with `p` prime and `CharP F p`.
- `coeff_rho_normPoly`: for `l < q`, the coefficient of `T^l` of `rho P x y (A(v))` is
  `(P_Y(x, y)^(-2))^l ∑_{j ≤ N, k < n} Q_l(B_{jk})(x, y) · (x^j y^k)^q`
  (from `coeff_rho_sum_mul_pow`).
- `coeff_rho_normPoly_eq_zero_of_E1L`: if `M ≤ q`, `P ∣ E1_l(v)` for all `l < M`, and
  `(x, y) ∈ F²` lies on `P = 0`, then the first `M` coefficients of `rho P x y (A(v))` vanish.
  Since `x^q = x`, `y^q = y`, the sum above is `E1_l(v)(x, y)`, which is a multiple of
  `P(x, y) = 0`.
- `exists_normPoly_rational` (`h₁`): under the hypotheses of `normPoly_resultant` (absolute
  irreducibility, `n d + m (n - 1)² < q`), irreducibility of `P`, `1 ≤ m`, `M ≤ q`, and the
  dimension inequality
  `∑_{l < M} (n (d + l(2m - 1) + N + 1) + m ((n - 1)(2l + 2) + 1 - n)) < n · n · (N + 1)(d + 1)`,
  there is `h ≠ 0` with `natDegree h ≤ (n - 1)(q + 1) m + n (d + qN)` such that
  `M · #T ≤ rootMultiplicity x h` for every `x ∈ F` and every finite `T ⊆ F` of `y` with
  `P(x, y) = 0 ≠ P_Y(x, y)`.
  Proof: `exists_ne_zero_forall_dvd` (`DivisibleKernel.lean`) gives `v ≠ 0` with
  `P ∣ E1_l(v)` for `l < M` (the left side bounds the codimensions of the conditions, the right
  side is the number of unknowns); `h = Res_Y(P, A(v))` is nonzero by `normPoly_resultant` and
  `resultant_ne_zero_of_not_dvd` (`RootTools.lean`); the multiplicity bound is
  `mul_card_le_rootMultiplicity_of_rho`.
- `coeff_rho_normPoly_eq_zero_of_E2L`: if `M ≤ q`, `P ∣ E2_{l,k}(v)` for `l < M`, `k < n - 1`,
  `g₀(x) ≠ 0`, and `y ∈ F̄` satisfies `P(x, y) = 0`, `P(x, y^q) = 0`, `y^q ≠ y`, then the first
  `M` coefficients of `rho P x y (A(v))` vanish. With `y' = y^q` the sum above is
  `∑_k e_{l,k}(x, y) y'^k`; multiplying by `g₀(x)` and using `P ∣ E2_{l,k}` gives
  `e_{l,n-1}(x, y) ∑_{k<n} ε_k(x, y) y'^k`, and `(y - y') ∑_k ε_k(x, y) y'^k = P(x, y) - P(x, y') = 0`
  (`divX_telescoping`, `RootTools.lean`) with `y ≠ y'`.
- `exists_normPoly_nonrational` (`h₂`): as `exists_normPoly_rational`, with the dimension
  inequality
  `(n - 1) ∑_{l < M} (n (d + l(2m - 1) + N + m + 1) + m ((n - 1)(2l + 2) + 1 - n)) < n · n · (N + 1)(d + 1)`;
  it gives `h ≠ 0` of the same degree bound with `M · #T ≤ rootMultiplicity x h` for every
  `x ∈ F` with `g₀(x) ≠ 0` and every finite `T ⊆ F̄` of `y` with `P(x, y) = 0 ≠ P_Y(x, y)`,
  `P(x, y^q) = 0` and `y^q ≠ y`.

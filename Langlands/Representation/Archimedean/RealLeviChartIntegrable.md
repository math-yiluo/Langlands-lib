# Proof of the integrability of the Gram bound on the opposite unipotent radical of a parabolic subgroup

Lean module: `Langlands.Representation.Archimedean.RealLeviChartIntegrable`.

Worker 5220 wrote this module for Task 6749 (`5dd3db87-6f14-4d0f-b9a7-3d0065415fd8`). It proves
`Langlands.Archimedean.RealLeviChartIntegrableStatement` (module
`RealLeviChartIntegralStatement`; see `RealLeviChartIntegralStatement.md` for the statement and
its notation). The proof is the theorem `Langlands.Archimedean.realLeviChartIntegrable`. The
matrix identities it uses are in the helper module `RealLeviChartGram` (see
`RealLeviChartGram.md`). The proof is internal; it follows no literature source. Unprefixed
names below are in the namespace `Langlands.Archimedean.RealLeviChartIntegrable`. `tm`, `colGram`
and `blockLower` are from `RealLeviChartGram`, and `gram` is `GramFormula.gram`.

## Overview

The statement is proved for an arbitrary monotone block function `cl : Fin N → ι` into a linear
order (`gen`), by strong induction on `N`. Let the first block have size `a` and write
`N = a + M`. The coordinates of the opposite unipotent radical split into the coordinates `X'` of
the chart of the remaining `M` positions and the `a × M` entries `V` below the first block. Then
`n̄(X) = [[1, 0], [W, B]]`, where `B = n̄(X')` and the columns of `W` are `V_0, …, V_{a-1}`. Write
`B = T κ` with `T` upper triangular and `κ` orthogonal. The substitution `V_k ↦ T V_k` has
Jacobian `1` and splits the integrand into a function `Kf` of `V` alone times the integrand of
the smaller chart. The integral of `Kf` is finite by peeling one column at a time, and each
column integral reduces to a constant `cInt M β` by a linear substitution. That constant is
finite by peeling one coordinate at a time.

The lemmas only bound lower Lebesgue integrals (`∫⁻`) from above. They use Mathlib's
`lintegral_map_le` and `lintegral_prod_le`, which need no measurability of the integrand.
Measurability is needed only in the final step, and there the integrand is continuous.

## Changes of variables (section `Measure`)

- `lintegral_le_comp`: `∫⁻ f dν ≤ ∫⁻ f ∘ g dμ` for a measure preserving `g : (α, μ) → (β, ν)`.
- `volume_univ_of_isEmpty`: if `κ` is empty, the space `κ → X` has volume `1`.
- `measurePreserving_curry`: currying `(κ₁ × κ₂ → ℝ) → (κ₁ → κ₂ → ℝ)` preserves Lebesgue
  measure. Both measures agree on boxes, which generate the σ-algebra (`Measure.pi_eq_generateFrom`).
- `lintegral_le_mulVec`: `∫⁻ f(u) du ≤ |det T| ∫⁻ f(T y) dy` for `det T ≠ 0`
  (`Real.map_matrix_volume_pi_eq_smul_volume_pi`). `measurePreserving_mulVec`: `y ↦ T y` preserves
  Lebesgue measure if `|det T| = 1`.
- `lintegral_le_mul_left`: `∫⁻ f(x) dx ≤ |s| ∫⁻ f(s t) dt` for `s ≠ 0`.
- `lintegral_add_sq_rpow_le`: for `A > 0` and real `δ`,
  `∫⁻ (A + x²)^δ dx ≤ A^{δ + 1/2} ∫⁻ (1 + t²)^δ dt` (substitute `x = √A t`).
- `lintegral_one_add_sq_rpow_lt_top`: `∫⁻ (1 + t²)^δ dt < ∞` for `δ < −1/2` (Mathlib's
  `integrable_rpow_neg_one_add_norm_sq`).

## The constant `cInt M β` (section `Constant`)

For `y ∈ ℝ^M` let `tail r y = 1 + ∑_{p ≥ r} y_p²` (`one_le_tail`, `tail_pos`), and for
`β : ℕ → ℝ` let

`cInt M β = ∫⁻_{ℝ^M} ∏_{r < M} (tail r y)^{β_r} dy`.

- `tm_one_add_vecMulVec_eq_tail`: `tm r (1 + y yᵀ) = tail r y`.
- `tail_cons_zero`, `tail_cons_succ`: for `y = (x, z)` with `x = y_0`,
  `tail 0 y = tail 0 z + x²` and `tail (r + 1) y = tail r z`.
- `prod_rpow_add_ite`: moving an extra factor `t_0^e` into the factor `r = 0` of the product
  `∏_{r < M} t_r^{b_r}` (for `M = 0` this needs `t_0 = 1`).
- `cInt_succ_le`: `cInt (M + 1) β ≤ C(β_0) · cInt M β'`, where `C(δ) = ∫⁻ (1 + t²)^δ dt` and
  `β'_r = β_{r+1} + [r = 0] (β_0 + 1/2)`. The variable `y_0 = x` is integrated first by
  `lintegral_add_sq_rpow_le` with `A = tail 0 z`. The factor `(tail 0 z)^{β_0 + 1/2}` it produces
  joins the factor `r = 0` of the remaining product.
- `cInt_lt_top`: `cInt M β < ∞` if `β_r ≤ −1/2` for all `r < M` and `β_0 < −1/2` when `M > 0`.
  The proof is induction on `M` with `cInt_succ_le`: `β'_0 = β_1 + β_0 + 1/2 < −1/2`, and
  `β'_r = β_{r+1} ≤ −1/2` for `r ≥ 1`. For `M = 0` the constant is the volume `1` of a point.

## The column peel (section `Columns`)

For `V : Fin a → Fin M → ℝ` (columns `V_0, …, V_{a-1} ∈ ℝ^M`) and `α, β : ℕ → ℝ`,

`Kf a M α β V = ∏_{j < a} det(1 + colGram j V)^{α_j} · ∏_{r < M} tm r (1 + colGram a V)^{β_r}`.

- `lintegral_tm_le`: for a positive semidefinite `M × M` matrix `G`,
  `∫⁻_u ∏_r tm r (1 + G + u uᵀ)^{β_r} du ≤ det(1 + G)^{1/2} · ∏_r tm r (1 + G)^{β_r} · cInt M β`.
  The Library's `TriangularUnitary.exists_upperTriangular_mul_conjTranspose` gives
  `1 + G = T Tᵀ` with `T` upper triangular and invertible. Substitute `u = T y`
  (`lintegral_le_mulVec`, `|det T| = det(1 + G)^{1/2}`). Then
  `1 + G + u uᵀ = T (1 + y yᵀ) Tᵀ`, and `tm_conj` gives
  `tm r (1 + G + u uᵀ) = (diagonalTail r T)² · tail r y = tm r (1 + G) · tail r y`.
- `Kf_succ_le`: `∫⁻ Kf (a' + 1) M α β ≤ cInt M β · ∫⁻ Kf a' M α β'`, where
  `β'_r = β_r + [r = 0] (α_{a'} + 1/2)`. Split off the last column, `V = Fin.snoc V' u`
  (`volume_preserving_piFinSuccAbove`). `colGram_snoc_of_le` and `colGram_snoc_succ` show that only
  the last product of `Kf` depends on `u`, through `colGram (a' + 1) V = colGram a' V' + u uᵀ`.
  Integrate `u` with `lintegral_tm_le` for `G = colGram a' V'`. Since `tm 0 = det`, the factors
  `det(1 + G)^{α_{a'}}` and `det(1 + G)^{1/2}` join the factor `r = 0` of the product
  (`prod_rpow_add_ite`).
- `Kf_lt_top`: `∫⁻ Kf a M α β < ∞` if `α_j ≤ −1/2` for `0 < j < a`, and, when `a > 0`,
  `β_r ≤ −1/2` for `r < M` and `β_0 < −1/2` if `M > 0`. The proof is induction on `a`. In the
  step, `cInt M β < ∞` by `cInt_lt_top`, and the new exponent
  `β'_0 = β_0 + α_{a'} + 1/2` is `< −1/2` when `a' > 0`. For `a = 0`, `Kf = 1` on a point.
  (`α_0` is never constrained, because `colGram 0 V = 0`.)

## Charts for a monotone block function (section `Chart`)

For `cl : Fin N → ι`:

- `CoordC cl` is the subtype of pairs `(p, q)` with `cl q < cl p`, and `lowerC cl X` is the matrix
  whose entry `(p, q)` is `X (p, q)` if `cl q < cl p`, `1` if `p = q`, and `0` otherwise. For
  `cl = RealLeviChart.cls sz` these are, by definition, `RealLeviChart.Coord sz` and
  `RealLeviChart.lower sz X`.
- For monotone `cl`: `lowerC_isLowerTriangular`, `det_lowerC` (`det = 1`), `isUnit_lowerC` and
  `gram_lowerC_pos` (`gram l (lowerC cl X) > 0`, from the Library's `GramFormula.gram_pos`).
- `continuous_lowerC`, `continuous_gram`, and `continuous_prod_gram`: the integrand
  `X ↦ ∏_l gram l (lowerC cl X)^{e_l}` is continuous (the bases are positive).

## The first-block peel (section `Peel`)

Here `cl : Fin (a + M) → ι`, with `cl` equal to `c0` on the first `a` positions and `> c0` on the
last `M` positions.

- `clR cl r = cl (a + r)` is the block function of the last `M` positions.
- `toCoord` maps a coordinate `(p, q)` of `clR cl` to `(a + p, a + q)` and a pair `(j, r)` in
  `Fin a × Fin M` to `(a + r, j)`. `toCoord_bijective`: this is a bijection
  `CoordC (clR cl) ⊕ (Fin a × Fin M) → CoordC cl`. No coordinate lies in the first block row, and
  every coordinate in the first block column has the form `(a + r, j)`.
- `embed e (X', V)` is the coordinate vector of `cl` with the values `X'` on the image of the left
  summand and `V j r` at `e (j, r)` (`embed_inl`, `embed_inr`). `measurePreserving_embed`: it
  preserves Lebesgue measure (`measurePreserving_piCongrLeft`,
  `volume_measurePreserving_sumPiEquivProdPi_symm`, `measurePreserving_curry`).
- `lowerC_embed`: `lowerC cl (embed e (X', V)) = blockLower V (lowerC (clR cl) X')`, checked entry
  by entry on the four blocks (`blockLower_castAdd_castAdd` and its three companions).
- `peel_le`: if `∫⁻ Kf a M γ (r ↦ γ_{a+r}) < ∞`, then
  `∫⁻_X ∏_{l < a+M} gram l (lowerC cl X)^{γ_l} ≤
  (∫⁻_V Kf a M γ (r ↦ γ_{a+r}) V) · ∫⁻_{X'} ∏_{r < M} gram r (lowerC (clR cl) X')^{γ_{a+r}}`.
  The proof changes variables by `embed` and uses `lintegral_prod_le`. For fixed `X'`, the
  Library's `TriangularUnitary.exists_upperTriangular_mul_unitary` gives
  `B = lowerC (clR cl) X' = T κ` with `T` upper triangular and `κ κᵀ = 1`. Since `det B = 1`,
  `(det T)² = 1`, so `V_k ↦ T V_k` preserves measure. After this substitution,
  `gram_blockLower_conj_of_le` gives `gram j = det(1 + colGram j V)` for `j < a`, and
  `gram_blockLower_conj_add` gives `gram (a + r) = gram r B · tm r (1 + colGram a V)`. So the
  integrand is `Kf a M γ (r ↦ γ_{a+r}) V · ∏_r gram r (B)^{γ_{a+r}}`.

## The induction (section `Induction`)

- `exists_first_block`: for monotone `cl : Fin N → ι` with `N > 0`, there is `a` with
  `1 ≤ a ≤ N`, `cl p = cl 0` for `p < a`, and `cl 0 < cl p` for `p ≥ a`. The proof takes
  `a = Nat.findGreatest`.
- `gen`: let `cl : Fin N → ι` be monotone and `γ : ℕ → ℝ` with `γ_l ≤ −1/2` for `0 < l < N` and
  `γ_l < −1/2` whenever `l = k + 1` and `cl k < cl l`. Then
  `∫⁻_X ∏_{l < N} gram l (lowerC cl X)^{γ_l} < ∞`. The proof is strong induction on `N`. For
  `N = 0`, the coordinate space is empty and the integral is `1`. For `N > 0`, take the first block
  `a` and write `N = a + M`. `Kf_lt_top` applies with `α = γ` and `β = (r ↦ γ_{a+r})`. In
  particular `γ_a < −1/2` when `M > 0`, because `cl (a − 1) = cl 0 < cl a`. The induction
  hypothesis applies to `clR cl` and `r ↦ γ_{a+r}`. Then `peel_le` bounds the integral by a product
  of two finite numbers.

## The theorem

`realLeviChartIntegrable : RealLeviChartIntegrableStatement`. Given `c`, `sz` and `γ`, the
function `cls sz` is monotone (from `RealLeviChart.lt_of_cls_lt`). Extend `γ` by `0` to `ℕ`, and
`gen` shows that the lower integral of the integrand is finite. The integrand is nonnegative and
continuous (`continuous_prod_gram`), so it is integrable (`hasFiniteIntegral_iff_ofReal`).

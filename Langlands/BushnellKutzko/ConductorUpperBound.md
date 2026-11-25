# The upper bound for the functional-equation exponent

## Setting

As in `ShellIdentity`: `K` is a `p`-adic field with canonical order `T.ord`
(`T = K.canonicalTopologicalData`), `N = n + 1`, `GL_N(K)` carries the Library Haar measure
`RankinSelberg.generalLinearHaar K.Carrier n`, `ψ` is a `UnitaryAdditiveCharacter K.Carrier`,
`ν` an `AdditiveHaarMeasure K.Carrier` with `SigmaFinite ν.measure`, and `σ` a complex
representation of `GL_N(K)` with
`GodementJacquet.Padic.NormalizedMatrixFunctionalEquationData K ψ ν σ 1 1 c a` (both Euler
polynomials `1`, unit `c`, exponent `a`). `𝓛` is a lattice chain in `K^N` with period
`e = 𝓛.period`, `𝔓^j(𝓛) = 𝓛.endFiltration j`, and `U^k(𝔄(𝓛)) = unitSubgroup K 𝓛 k`.
`ordOf hϖ` is the order function attached to a uniformizer `ϖ` (module `SplittingBasis`).

## Declarations

- `ord_coe_unit`: units of `𝔬_K` have canonical order `0`.
- `ord_coe_of_irreducible`: every uniformizer of `𝔬_K` has canonical order `1`.
- `ordOf_eq_ord`: for a uniformizer `ϖ` and `x ≠ 0`, `ordOf hϖ x = T.ord x`.
- `card_mul_le_period_mul_ord_det`: if `toLin' X ∈ 𝔓^j(𝓛)` and `det X ≠ 0`, then
  `N j ≤ e · ord(det X)`.
- `ord_det_inv_smul_transpose`: for `t ≠ 0` and `g ∈ GL_N(K)`,
  `ord(det(t⁻¹ gᵀ)) = ord(det g) - N ord(t)`.
- `toLin'_inv_smul_transpose_mem_of_fourier_ne_zero`: let `k ≥ 1`, `t ≠ 0` with `x ↦ ψ(t x)`
  nontrivial on `𝔬_K`, `j ≤ 1 - k` and `t⁻¹ b' ∈ 𝔓^j(𝓛)`. If the Fourier transform
  `rectangularFourierIntegral ψ ν (stratumTest K 𝓛 hk ψ b')` of the stratum test function
  (module `StratumZetaIntegral`) is nonzero at a matrix `x`, then `t⁻¹ xᵀ ∈ 𝔓^j(𝓛)`.
- `exists_ord_det_eq_of_stratum` (the stratum on the shell): under the functional-equation data
  above, let `k ≥ 1`, let `w` be a smooth vector with `σ(g) w = ψ(tr(b'(g - 1))) w` for all
  `g ∈ U^k(𝔄(𝓛))`, let `ℓ` be a smooth functional (`SmoothDual σ`) with `ℓ(w) ≠ 0`, and let
  `t, j` be as in the previous item. Then some `g ∈ GL_N(K)` has `ord(det g) = -a`,
  `t⁻¹ gᵀ ∈ 𝔓^j(𝓛)`, `ℓ(σ(g^{-T}) w) ≠ 0` (`g^{-T}` is
  `GeneralLinear.inverseTranspose (n + 1) K.Carrier g`) and `t⁻¹ (gᵀ - b') ∈ 𝔓^{1-k}(𝓛)`.
  The last conclusion is used by the lower bound (module `ConductorLowerBound`).
- `period_mul_le_of_stratum` (the upper bound): under the same hypotheses,
  `e a ≤ -N j - e N ord(t)`.

When `ψ` is trivial on `𝔬_K` but not on `𝔭_K^{-1}`, `t = ϖ⁻¹` (so `ord(t) = -1`) and `j = -m`
with `m ≥ k - 1`, the bound reads `e a ≤ N (e + m)`, that is `a ≤ N (1 + m/e)`. The positive-level
case of T2 uses it with `[𝔄(𝓛), m, m - 1, b]` a stratum contained in `σ` and
`b' = ϖ⁻¹ b`.

## Provenance

The estimate `a ≤ N (1 + m/e)` is an internal step towards recovering the exponent
formula of Bushnell (1987), Theorem 3, and Bushnell–Fröhlich (1985), (3.3.8). The proof
uses coefficient extraction on one determinant shell and a support inclusion for the
Fourier transform of the test function.

## Proof

`ord_coe_unit`: a unit `w` and its inverse are integral, so both have order `≥ 0`
(`RankinSelberg.UnramifiedUnitary.mem_integers_iff_ord`), and their orders sum to `0`.
`ord_coe_of_irreducible`: write the canonical uniformizer `T.uniformizer` (order `1`) as
`ϖ^d u` with `u` a unit (`exists_eq_zpow_ordOf_mul`); then `d ord(ϖ) = 1` with `ord(ϖ) ≥ 0`,
so `ord(ϖ) = 1`. `ordOf_eq_ord`: write `x = ϖ^{ordOf x} u` and take orders.
`card_mul_le_period_mul_ord_det` is `LatticeChain.card_mul_le_period_mul_ordOf_det` (module
`CompactLevelBound`) for some uniformizer, rewritten with `ordOf_eq_ord` and
`LinearMap.det_toLin'`. `ord_det_inv_smul_transpose` uses `det(t⁻¹ gᵀ) = t^{-N} det g`.

`toLin'_inv_smul_transpose_mem_of_fourier_ne_zero`: the Fourier support lemma
`LatticeChain.toLin'_mem_endFiltration_of_rectangularFourierIntegral_ne_zero` (module
`FourierSupport`) gives `t⁻¹ (xᵀ - b') ∈ 𝔓^{1-k}(𝓛) ⊆ 𝔓^j(𝓛)`; add `t⁻¹ b' ∈ 𝔓^j(𝓛)`.

`exists_ord_det_eq_of_stratum`: the previous lemma and `card_mul_le_period_mul_ord_det` show that
the Fourier transform of the stratum test function vanishes at `g` unless
`ord(det g) ≥ N ord(t) + min(N j, 0)` (for `d = ord(det g) - N ord(t) < 0` one has `e d ≤ d`, as
`e ≥ 1`). The stratum coefficient `g ↦ ℓ(σ(g) w)` has the constant shifted rational value
`vol(U^k(𝔄(𝓛))) ℓ(w) ≠ 0` (`hasShiftedRationalValue_stratumTest`,
`generalLinearHaar_real_unitSubgroup_pos`). `exists_ord_det_eq_of_functionalEquation` (module
`ShellIdentity`) then gives `g` on the shell `ord(det g) = -a` where both the Fourier transform
and `ℓ(σ(g^{-T}) w)` are nonzero. The previous lemma places `t⁻¹ gᵀ` in `𝔓^j(𝓛)`, and the
Fourier support lemma it is built on places `t⁻¹ (gᵀ - b')` in `𝔓^{1-k}(𝓛)`.

`period_mul_le_of_stratum`: apply `card_mul_le_period_mul_ord_det` to `t⁻¹ gᵀ` for this `g`:
`N j ≤ e (ord(det g) - N ord(t)) = e (-a - N ord(t))`.

# Points supported at one finite place

Module `Langlands.Global.RankinSelberg.LocalPointFactorization`, namespace
`Langlands.Global.RankinSelbergGlobal.LocalPointFactorization`.

## Content

General lemmas for the one-place step of the unramified Euler factorizations of the global
Rankin–Selberg integrals. `localPoint F m v h` (written `ι_v(h)`) is the point of
`GL_m(𝔸)` with component `h ∈ GL_m(F_v)` at the finite place `v` and the identity at every
other place. It is defined in `WhittakerCellDecompositionStatement`.
`finiteComponent F m v g` is the component `g_v` of `g` at `v`. `torus ϖ λ` is the diagonal
matrix `ϖ ^ λ = diag(ϖ ^ λ_1, …, ϖ ^ λ_m)`.

### Local lemmas over a valued field

`K` is a field with a valuation `w`, `ϖ ∈ Kˣ` is uniformizing for `w`
(`IsUniformizingElement w ϖ`), and `exponent hϖ g` is the Library's Iwasawa exponent of
`g ∈ GL_(n+1)(K)` (the unique `λ` with `g ∈ N ϖ ^ λ GL_(n+1)(𝒪)`).

- `torus_zero`: `ϖ ^ 0 = 1`.
- `torus_mul_mul_inv_mem`: conjugation by `ϖ ^ λ` maps the upper unitriangular group
  `N_(n+1)(K)` to itself.
- `exponent_torus_mul`: for `u ∈ N_(n+1)(K)` and `k ∈ GL_(n+1)(𝒪_w)` (the Library's
  `integralSubgroup`), the exponent of `ϖ ^ λ u k` is `λ`.
- `exponent_unipotent_mul_integral`: the exponent of `u k` is `0`.
- `cellFunction_mul_cellFunction`: let `θ`, `θ'` be characters of `N_(n+1)(K)` with
  `θ(u) θ'(u) = 1` for all `u`. Then the product of the Library's cell functions
  `cellFunction hϖ θ c g * cellFunction hϖ θ' c' g` is
  `(c(λ) if λ is antitone, else 0) · (c'(λ) if λ is antitone, else 0)` with
  `λ = exponent hϖ g`. The characters cancel, so no integrality condition on `θ` is used.
- `sphericalWhittaker_mul_sphericalWhittaker`: for such `θ`, `θ'`, any natural number `q`,
  tuples `a, b : Fin (n + 1) → ℂˣ` and `g` of exponent `λ`, the product
  `W°_θ(g; a) W°_θ'(g; b)` of the Library's spherical Whittaker functions
  `sphericalWhittaker hϖ θ q a` is
  `(halfModulus q λ · satakeSchur a λ if λ is antitone, else 0) ·
  (halfModulus q λ · satakeSchur b λ if λ is antitone, else 0)`.
- `sphericalWhittaker_mul_sphericalWhittaker_of_exponent_eq_zero`: if the exponent of `g`
  is `0`, the product is `1`.
- `isUniformizingElement_of_isEquiv`: equivalent valuations have the same uniformizing
  elements.
- `integer_eq_of_isEquiv`: equivalent valuations have the same ring of integers.

### Points supported at one finite place

- `finite_ofFinite`, `infinite_ofFinite`: the finite and infinite parts of
  `AdelicGL.ofFinite x` are `x` and `1`.
- `adelicEquiv_localPoint`: the matrix of `ι_v(h)` is
  `AdelicGL.ofFinite (FiniteAdelicGL.localInclusion v h)`.
- `RankinSelbergGlobal.finiteComponent_mul` from `PartialIntegralExhaustion` and
  `finiteComponent_inv`: `g ↦ g_v` is a group homomorphism.
- `finiteComponent_localPoint`: `ι_v(h)_v = h`. `finiteComponent_localPoint_of_ne`: for
  `w ≠ v`, `ι_v(h)_w = 1`.
- `localPoint_mul`: `ι_v(h h') = ι_v(h) ι_v(h')`.
- `localPoint_mul_comm`: if `g_v = 1`, then `ι_v(h) g = g ι_v(h)`.
- `finiteComponent_mul_inv_localPoint`: `(g ι_v(g_v)⁻¹)_v = 1`.
- `localPoint_mul_eq`: `ι_v(h) g = g' ι_v(h g_v)` with `g' = g ι_v(g_v)⁻¹`. Together with
  the previous lemma this puts `ι_v(h) g` in the form `g' ι_v(h')` with `g'_v = 1` used by
  the Library's statement `UnramifiedWhittakerFactorizationStatement`.

### The uniformizer of `F_v`

- `isUniformizingElement_of_eq_exp`: for a `ℤᵐ⁰`-valued valuation, an element of value
  `exp(-1)` is uniformizing.
- `placeUniformizer v : (F_v)ˣ` is the uniformizer of the local realization
  `CompletionPadic.topologicalData v` (the Library's `PadicAbelian.uniformizerUnit`). It is
  a fixed choice of uniformizer at each place.
- `valued_placeUniformizer`: its value for the completion valuation `Valued.v` is
  `exp(-1)`. `isUniformizingElement_valued`: it is uniformizing for `Valued.v`.
- `valued_isEquiv_canonical`: `Valued.v` is equivalent to the canonical valuation of
  `padicField v`. `isUniformizingElement_canonical`: `ϖ_v` is uniformizing for the
  canonical valuation as well. This is the valuation in
  `UnramifiedWhittakerFactorizationStatement`; `Valued.v` is the one in
  `WhittakerCellDecompositionStatement`.
- `norm_placeUniformizer`: `‖ϖ_v‖ = N(v)⁻¹`, where `N(v) = Ideal.absNorm v.asIdeal`.
- `exists_eq_mul_of_isUnipotentIntegral`: if `x ∈ GL_(m+1)(F_v)` satisfies the Library's
  `IsUnipotentIntegral` (that is, `x ∈ N(F_v) GL(𝒪_v)`), then `x = u k` with `u`
  unitriangular and `k` in `GL_(m+1)` of the integers of the canonical valuation.

### The determinant

`detNorm F m g = |det g|_𝔸` and `detPower F m g s = exp(s · log |det g|_𝔸)` are the
Library's adelic determinant norm and its complex power.

- `detNorm_localPoint`: `|det ι_v(h)|_𝔸 = ‖det h‖_v`.
- `detNorm_mul`, `detNorm_ne_zero`: `|det|_𝔸` is multiplicative and nonzero.
- `detPower_localPoint_mul`:
  `detPower (ι_v(h) g) s = exp(s · log ‖det h‖_v) · detPower g s`.
- `log_norm_det_torus`: `log ‖det ϖ_v ^ λ‖_v = -(∑_i λ_i) · log N(v)`.

## Provenance

Internal supporting results, used for the proofs of the partial Euler factorizations of the
global Rankin–Selberg integrals (Cogdell 2004, *Analytic theory of L-functions for GL_n*,
in Bernstein–Gelbart, *An introduction to the Langlands program*: §2.2, printed p.206;
§2.3, p.210; Theorem 3.3, p.215). At an unramified place `v` the global integral is
computed cell by cell in the Iwasawa decomposition
`GL_n(F_v) = ⊔_λ N_n(F_v) ϖ ^ λ GL_n(𝒪_v)`. The lemmas here are the group-theoretic and
valuation-theoretic facts this needs: the exponent of a translated cell, the product of
the spherical Whittaker functions for `ψ_v` and `ψ_v⁻¹`, the adelic points concentrated at
`v`, a uniformizer valid for both valuations of `F_v` used in the Library, and the
determinant. None of them is a statement from the literature; each is a direct consequence
of Library definitions.

## Proof

- **Exponents.** `torus_mul_mul_inv_mem` computes the entries of `ϖ ^ λ u ϖ ^ (-λ)` with
  the Library's `diagonalUnits_mul_mul_apply`: entry `(i, j)` is
  `ϖ ^ λ_i u_ij ϖ ^ (-λ_j)`, so the zero and unit patterns of `u` are kept. Then the
  Library's uniqueness theorem `exponent_eq` applies to
  `ϖ ^ λ u k = (ϖ ^ λ u ϖ ^ (-λ)) ϖ ^ λ k` (and to `u k = u ϖ ^ 0 k`).
- **Products of cell functions.** Unfold `cellFunction`. On the antitone branch the product
  contains `θ(n) θ'(n) = 1` for the unipotent part `n` of `g`. `sphericalWhittaker` is a
  cell function with coefficient `halfModulus q λ · satakeSchur a λ`. For exponent `0` the
  Library's `halfModulus_zero` and `satakeSchur_zero` give `1`.
- **Valuations.** `isUniformizingElement_of_isEquiv` transports `w(ϖ) < 1` with
  `IsEquiv.lt_one_iff_lt_one` and `w(x) = w(ϖ) ^ m` with `IsEquiv.eq_iff` (after
  `map_zpow₀`). `integer_eq_of_isEquiv` is `IsEquiv.le_one_iff_le_one`.
- **Points at one place.** The components are computed with the Library's
  `localProjection_localInclusion` and `localProjection_localInclusion_of_ne`. For the
  commutation, the matrices of `ι_v(h) g` and `g ι_v(h)` are compared through
  `AdelicGL.pair_projections` (infinite and finite parts) and
  `FiniteAdelicGL.ext_localProjection` (place by place): at `w = v` the component of `g`
  is `1`, and at `w ≠ v` that of `ι_v(h)` is `1`. `localPoint_mul_eq` then follows by
  group manipulation.
- **Uniformizer.** `uniformizerUnit_zpow_value` with exponent `1` gives value `exp(-1)`
  for the discrete valuation of the realization. That valuation is `Valued.v`
  (`topologicalData_discreteValuation`). The equivalence with the canonical valuation is
  the Library's `valuativeRel_valuation_isEquiv`. The norm is
  `HeckeEulerProduct.norm_uniformizerUnit`.
- **`N(F_v) GL(𝒪_v)`.** `IsUnipotentIntegral` supplies `k₀ ∈ GL(𝒪_v)` with `x k₀`
  unitriangular. Take `u = x k₀` and `k = k₀⁻¹`. The integrality of `k₀⁻¹` comes from
  `FiniteAdelicGL.mem_localIntegral` (entries of `k₀` and `k₀⁻¹` have `Valued.v ≤ 1`),
  transported to the canonical valuation by `integer_eq_of_isEquiv`.
- **Determinant.** `detNorm_localPoint` is the Library's
  `coe_determinantNorm_localInclusion`. Then `Real.log_mul` and `Complex.exp_add` give
  `detPower_localPoint_mul`. For `log_norm_det_torus`: `det ϖ ^ λ = ∏_i ϖ ^ λ_i`
  (`Matrix.det_diagonal`), `‖ϖ ^ λ_i‖ = N(v) ^ (-λ_i)` and `Real.log_prod`.

The zero-torus identity is reused as `GeneralLinear.torus_zero` from
`PrincipalLevelDominance`; determinant multiplicativity is reused as
`Unfolding.detNorm_mul` from `UnfoldingGL`.

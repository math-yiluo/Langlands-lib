# The transposed-coefficient recursion for the block Jacquet functional

Lean module: `Langlands.Representation.Archimedean.RealReverseRecursion`.

Worker 5 wrote this module for Task 7069 (`79f2a631-6cbb-4805-97c7-163e69df5de3`), the proof of
`RealStandardIrreducibleCriterionStatement`. It is the inductive core of the reversal statement
for character lists with ties (`RealCharacterReverseKernel`). It runs Worker 5220's recursion for
the block Jacquet functional (`RealBlockFunctional.jac_eq_zero`, Task 6749) on matrix
coefficients evaluated at transposed arguments, in place of the orthogonality relation
`∫ u h = 0`.

Notation: `GL_N(ℝ)` is `Langlands.GeneralLinear N ℝ`, `O(N)` is `unitaryCompact ℝ N` with the
Haar probability measure `RealPrincipalSeriesDuality.haarK N`. `R(g)` is
`Whittaker.rightTranslation ℂ _ g` (`R(g) f (x) = f(x g)`). `gᵀ` is
`RealReverseTwist.transposeGL g`. `diag(g₁, g₂)` is `blockDiagGL g₁ g₂`, the block-diagonal matrix
of `RealBlockParabolic.blockDiag`, and `d(s) = dTail s = diag(1_a, s·1_{k+1})` (module
`RealBlockLimit`). From `RealBlockJacquet`: `IsBlockDominant`, `blockStep`,
`blockPair φ h g₁ = ∫_{O(k+1)} φ(κ₂) blockStep h (diag(g₁, κ₂)) dκ₂`, and
`blockShiftChar k χ l x = χ_l(x) |x|^{−(k+1)/2}`. From `RealBlockDual`:
`restrictBlock u = (g₁ ↦ u(diag(g₁, 1)))` and `blockDualChar`. From `RealBlockFunctional`:
`dim`, `BlockOrdered`, `TiedIrreducible`, `blockVector` and the block Jacquet functional `jac`.
From `RealBlockLimitValue`: `seqUnit m = m + 1`, `tailFactor` and `limitValue`.
`IsSignedPower χ e` (module `PartialJacquetIntegral`) means `χ_l(x) = χ_l(sgn x) |x|^{e_l}`,
`χ_l(1) = 1` and `‖χ_l(−1)‖ = 1`; `dualChar χ` is `l, x ↦ (χ_l x)⁻¹`.

Declarations without a prefix are in the namespace `Langlands.Archimedean.RealReverseRecursion`.
The module contains one Prop-valued definition, the auxiliary predicate `IsLimitConstant`; it is
not a statement of a result.

## Definitions

* `coeff x y g = ∫_{O(n)} x(κ g) y(κ) dκ`, the matrix coefficient of the pair `(x, y)`.
* `nullCoeff χ U` (for a space `U` of functions on `GL_n(ℝ)`): the span of the coefficients
  `coeff x y` with `x` an `O(n)`-finite function of `principalSeries ℝ n (dualChar χ)`, `y` an
  `O(n)`-finite function of `principalSeries ℝ n χ`, and `∫_{O(n)} u(κ) y(κ) dκ = 0` for every
  `u ∈ U`.
* `IsLimitConstant a k c`: the conclusion of `RealBlockLimitValue.exists_tendsto` for the
  constant `c`. For all `χ, e` with `IsSignedPower χ e` and `IsBlockDominant e a k`, all `u` in
  `principalSeries ℝ (a+(k+1)) (dualChar χ)` and all `h` in `principalSeries ℝ (a+(k+1)) χ`,
  `(c · tailFactor a k χ (m+1))⁻¹ ∫_{O(a+k+1)} u(κ d(m+1)) h(κ) dκ → limitValue u h` as `m → ∞`.

## Results

### Transposes

* `blockDiag_transpose`: `(blockDiag A D)ᵀ = blockDiag Aᵀ Dᵀ`.
* `transposeGL_blockDiagGL`: `diag(g₁, g₂)ᵀ = diag(g₁ᵀ, g₂ᵀ)`.
* `transposeGL_dTail`: `d(s)ᵀ = d(s)`.
* `transposeGL_dTail_mul`: `(d(s) diag(g₁, 1))ᵀ = d(s) diag(g₁ᵀ, 1)`.

### Limits of coefficients

* `coeff_dTail_mul`: `coeff x y (d(s) diag(g₁, 1)) = ∫ R(diag(g₁, 1)) x (κ d(s)) · y(κ) dκ`.
* `limitValue_rightTranslation` (assumes `RealBlockChartIntegrableStatement`): let
  `IsSignedPower χ e` and `IsBlockDominant e a k`. Suppose `x` has a finite separation of
  variables `x(diag(h, g₂)) = ∑ᵢ rᵢ(h) bᵢ(g₂)` with continuous `rᵢ` on `GL_a(ℝ)` and `bᵢ` on
  `GL_{k+1}(ℝ)` (finite index type `ι`). Let `y` be `O(a+k+1)`-finite in
  `principalSeries ℝ (a+(k+1)) χ`. Then for every `g₁ ∈ GL_a(ℝ)`

  `limitValue (R(diag(g₁, 1)) x) y = ∑ᵢ coeff rᵢ (blockPair bᵢ y) g₁`.

* `exists_tendsto_nullCoeff` (assumes `RealBlockChartIntegrableStatement` and
  `RealBlockParabolicIntegrationStatement`): let `IsSignedPower χ e`, `IsBlockDominant e a k`,
  let `principalSeries ℝ (k+1) (blockDualChar a χ)` be irreducible, and let `IsLimitConstant a k c`.
  Let `U` be a space of `O(a+k+1)`-finite functions of `principalSeries ℝ (a+(k+1)) (dualChar χ)`,
  stable under right translation by `O(a+k+1)` and under all right derivatives. Then for every
  `F ∈ nullCoeff χ U` there is `G ∈ nullCoeff (blockShiftChar k χ) (U.map restrictBlock)` with

  `(c · tailFactor a k χ (m+1))⁻¹ · F(d(m+1) diag(g₁, 1)) → G(g₁)` as `m → ∞`, for every
  `g₁ ∈ GL_a(ℝ)`.

### The recursion

`jac_eq_zero_of_transpose` (assumes `RealBlockChartIntegrableStatement`,
`RealBlockParabolicIntegrationStatement` and `RealBlockFunctional.TiedIrreducible`). Let `ks` be a
list of block parameters, `n = dim ks`, `χ` characters and `e` exponents with `IsSignedPower χ e`,
`p : ℕ → ℕ` with `χ_l(−1) = (−1)^{p_l}` for all `l`, and `BlockOrdered ks e`. Let `U` and `X` be
spaces of `O(n)`-finite functions of `principalSeries ℝ n (dualChar χ)`, both stable under right
translation by `O(n)` and under all right derivatives, with `U ≠ 0`. Let `f` be an `O(n)`-finite
function of `principalSeries ℝ n χ` such that, for every `x ∈ X`, the function
`g ↦ coeff x f (gᵀ)` lies in `nullCoeff χ U`. Then

`x(1) · jac ks e p f = 0` for every `x ∈ X`.

Provenance. Derived, internal infrastructure. It is the leading-term (Langlands lemma) recursion
along the maximal parabolic subgroups of a block decomposition, as in
`RealBlockFunctional.jac_eq_zero`, applied to transposed matrix coefficients; the transposition
device is the one of Worker 5677's complex reversal argument (`ComplexReverseRecursion`, Task
7064). The module makes no claim beyond the Lean statements.

## Proof

The transpose lemmas are entrywise: transposition of `Matrix.fromBlocks` swaps the off-diagonal
blocks (here zero) and transposes the diagonal blocks; `d(s)` is diagonal; and `d(s)` commutes
with `diag(g₁, 1)` (`blockDiagGL_mul_dTail`). `coeff_dTail_mul` is associativity:
`R(diag(g₁, 1)) x (κ d(s)) = x((κ d(s)) diag(g₁, 1)) = x(κ (d(s) diag(g₁, 1)))`.

`limitValue_rightTranslation`. For `κ₁ ∈ O(a)` and `κ₂ ∈ O(k+1)`,
`R(diag(g₁, 1)) x (diag(κ₁, κ₂)) = x(diag(κ₁ g₁, κ₂)) = ∑ᵢ rᵢ(κ₁ g₁) bᵢ(κ₂)`. Hence the inner
`κ₂`-integral of `limitValue` is `∑ᵢ rᵢ(κ₁ g₁) · blockPair bᵢ y (κ₁)`, and the outer `κ₁`-integral
is `∑ᵢ coeff rᵢ (blockPair bᵢ y) g₁`. Sums and integrals commute (`integral_finsetSum`) because all
integrands are continuous on compact groups with probability measures
(`integrable_of_continuous`). Continuity of `κ₂ ↦ blockStep y (diag(κ₁, κ₂))` is
`RealBlockJacquet.continuous_blockStep`, and continuity of `blockPair bᵢ y` comes from
`blockPair_mem` (which uses `RealBlockChartIntegrableStatement`).

`exists_tendsto_nullCoeff`, by induction over the span (`Submodule.span_induction`).

* Generator `F = coeff x y` with `y ⊥ U`. Apply
  `RealBlockSliceDecomposition.exists_blockDiag_decomposition` to `x`:
  `x(diag(h, g₂)) = ∑ᵢ ỹᵢ(diag(h, 1)) bᵢ(g₂)` with `ỹᵢ` `O(a+k+1)`-finite in the principal series
  of `χ⁻¹` and `bᵢ` `O(k+1)`-finite in that of `blockDualChar a χ`. Put
  `G = ∑ᵢ coeff (restrictBlock ỹᵢ) (blockPair bᵢ y)`. Each term is a generator of
  `nullCoeff (blockShiftChar k χ) (U.map restrictBlock)`: `restrictBlock ỹᵢ` is `O(a)`-finite in
  the principal series of `(blockShiftChar k χ)⁻¹` (`RealBlockDual.restrictBlock_mem`),
  `blockPair bᵢ y` is `O(a)`-finite in that of `blockShiftChar k χ`
  (`RealBlockJacquet.blockPair_mem`), and
  `∫_{O(a)} restrictBlock u · blockPair bᵢ y = 0` for all `u ∈ U` by
  `RealBlockDual.integral_restrictBlock_mul_blockPair_eq_zero` (with `φ = bᵢ`; it uses the
  irreducibility of the tied block and the stability of `U`). For the limit, by
  `coeff_dTail_mul` the normalized `F(d(m+1) diag(g₁, 1))` is the normalized coefficient of the
  pair `(R(diag(g₁, 1)) x, y)` along `d(m+1)`. By `IsLimitConstant` it tends to
  `limitValue (R(diag(g₁, 1)) x) y`, which is `G(g₁)` by `limitValue_rightTranslation`.
* `0`, sums and scalar multiples: take `G = 0`, `G₁ + G₂`, `r • G`; limits are compatible with
  these operations.

`jac_eq_zero_of_transpose`, by induction on `ks`.

* `ks = []`: `GL_0(ℝ)` is trivial, so every function is determined by its value at `1`, and the
  integral over `O(0)` is evaluation at `1`. Since `U ≠ 0`, some `u ∈ U` has `u(1) ≠ 0`. Every `y`
  orthogonal to `U` then has `y(1) = 0`, so `y = 0` and all generators of `nullCoeff χ U` vanish:
  `nullCoeff χ U = 0`. Hence `0 = coeff x f (1ᵀ) = x(1) f(1) = x(1) · jac [] e p f`.
* `ks = k :: ks'`, `a = dim ks'`. Let `φ = blockVector a k e p`, an `O(k+1)`-finite function of
  the principal series of `blockDualChar a χ` (`blockVector_mem`). `TiedIrreducible`, applied to
  `blockDualChar a χ` (exponents `−e_{a+l} − a/2`, signs `p_{a+l}`, equal real parts by
  `IsBlockDominant.tie`; `isSignedPower_blockDualChar`, `blockDualChar_neg_one`), says that this
  principal series is irreducible. By `RealBlockDual.map_restrictBlock`, `U' = U.map restrictBlock`
  is a nonzero stable space of `O(a)`-finite functions of the principal series of
  `(blockShiftChar k χ)⁻¹`. If `X = 0` the claim is trivial. Otherwise `X' = X.map restrictBlock`
  is stable in the same way. Take `c` with `IsLimitConstant a k c` from
  `RealBlockLimitValue.exists_tendsto`. Apply the induction hypothesis on `GL_a(ℝ)` to
  `blockShiftChar k χ` (signed power with exponents `e − (k+1)/2` and the same signs:
  `isSignedPower_blockShift`, `blockShiftChar_neg_one`, `BlockOrdered.shift`), `U'`, `X'`,
  `f' = blockPair φ f` (`blockPair_mem`) and `restrictBlock x ∈ X'`. Its conclusion
  `restrictBlock x (1) · jac ks' (e − (k+1)/2) p (blockPair φ f) = 0` is
  `x(1) · jac (k :: ks') e p f = 0` (`jac_cons`, `diag(1, 1) = 1`).

  It remains to check the hypothesis of the induction hypothesis: for `x₀ ∈ X`, the function
  `g₁ ↦ coeff (restrictBlock x₀) (blockPair φ f) (g₁ᵀ)` lies in
  `nullCoeff (blockShiftChar k χ) U'`.
  By `RealBlockSliceDecomposition.exists_mem_blockDiag_eq` there is `x' ∈ X` with
  `x'(diag(h, g₂)) = x₀(diag(h, 1)) φ(g₂)`. By hypothesis `F = (g ↦ coeff x' f (gᵀ))` lies in
  `nullCoeff χ U`, so `exists_tendsto_nullCoeff` gives `G ∈ nullCoeff (blockShiftChar k χ) U'`
  with normalized `F(d(m+1) diag(g₁, 1)) → G(g₁)`. On the other hand,
  `F(d(s) diag(g₁, 1)) = coeff x' f (d(s) diag(g₁ᵀ, 1))` (`transposeGL_dTail_mul`), so by
  `coeff_dTail_mul` and `IsLimitConstant` the same normalized sequence tends to
  `limitValue (R(diag(g₁ᵀ, 1)) x') f`. By `limitValue_rightTranslation` (one-term separation
  `r = restrictBlock x₀`, `b = φ`), this equals `coeff (restrictBlock x₀) (blockPair φ f) (g₁ᵀ)`.
  Uniqueness of limits (`tendsto_nhds_unique`) identifies it with `G(g₁)`. So the function is `G`,
  which lies in `nullCoeff (blockShiftChar k χ) U'`.

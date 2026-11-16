# The block Jacquet functional on `GL_n(ℝ)` and its vanishing on proper submodules

Lean module: `Langlands.Representation.Archimedean.RealBlockFunctional`.

Worker 5220 wrote this module for Task 6749 (`5dd3db87-6f14-4d0f-b9a7-3d0065415fd8`), the proof
of `RealStandardLanglandsQuotientStatement` (module `RealLargeLanglandsQuotientReduction`). It
generalizes the published `JacquetDual` and `JacquetKernel` (strictly decreasing exponents, one
row at a time) to block decompositions in which the exponents are tied within each block and
strictly decrease between blocks. It assembles the recursion from `RealBlockJacquet` (the
function `blockPair`) and `RealBlockDual` (the dual step). The module is the real analogue of
Worker 140's `ComplexBlockFunctional` (Task 7063) and follows its structure.

Notation: `GL_N(ℝ)` is `Langlands.GeneralLinear N ℝ` and `O(N)` is `unitaryCompact ℝ N`, with the
Haar probability measure `RealPrincipalSeriesDuality.haarK N`. `IsSignedPower χ e` (module
`PartialJacquetIntegral`) means `χ_l(x) = χ_l(sgn x) |x|^{e_l}`, `χ_l(1) = 1` and
`‖χ_l(−1)‖ = 1`; `GramFormula.signUnit x` is the sign of `x`, and `dualChar χ = (l, x) ↦ (χ_l x)⁻¹`.
`signVector n e p a` (module `JacquetNonvanishing`) is the principal-series function whose
restriction to `O(n)` is the sign monomial `κ ↦ ∏_l κ_ll^{p_l + 2 a_l}`. `blockPair`,
`blockShiftChar`, `IsBlockDominant`, `blockPairOn` and `blockPair_mem` come from `RealBlockJacquet`;
`blockDualChar`, `map_restrictBlock` and `integral_restrictBlock_mul_blockPair_eq_zero` from
`RealBlockDual`; `annihilator` and its lemmas from the Library's `JacquetKernel`. Unprefixed names
below are in the namespace `Langlands.Archimedean.RealBlockFunctional`.

## Definitions

* `dim ks`: for a list `ks` of block parameters (block sizes `k + 1`, the last block first),
  `dim [] = 0` and `dim (k :: ks) = dim ks + (k + 1)`.
* `BlockOrdered ks e`: for `ks = k :: ks'`, `IsBlockDominant e (dim ks') k` holds (the exponents at
  positions `dim ks', …, dim ks' + k` have equal real parts; the real parts decrease weakly before
  position `dim ks'` and strictly at that position), and recursively `BlockOrdered ks' e`.
  `BlockOrdered [] e` is `True`.
* `TiedIrreducible`: for every `b`, every signed-power `ψ` with exponents `f`, signs
  `ψ_l(−1) = (−1)^{q_l}` (`q : ℕ → ℕ`) and `Re f_l = Re f_0` for `l < b`, the
  `(𝔤𝔩_b(ℝ), O(b))`-module `(principalSeriesRep ℝ b ψ, principalSeriesLie ℝ b ψ)` is irreducible.
  The sign hypothesis matters: `IsSignedPower` only asks `‖ψ_l(−1)‖ = 1`, and if `ψ_l(−1) ∉ {±1}` for some
  `l < b`, the principal series is `0`. The Library's `RealTemperedStandardIrreducibleStatement` is the
  corresponding statement for real standard modules.
* `blockVector a k e p = signVector (k+1) (l ↦ −(e_{a+l} + a/2)) (l ↦ p_{a+l}) 0`: a sign vector
  of the dual principal series of the block at positions `a, …, a+k` (`blockVector_mem`).
* `jac ks e p h` (the block Jacquet functional): `jac [] e p h = h(1)` and
  `jac (k :: ks) e p h = jac ks (e − (k+1)/2) p (blockPair (blockVector (dim ks) k e p) h)`.

## The statement

`RealBlockFunctionalStatement` assumes three statements: `RealBlockChartIntegrableStatement`,
`RealBlockParabolicIntegrationStatement` and `TiedIrreducible`. None of them is proved here.
Under these assumptions it says the following.

Let `χ` be characters with exponents `e` and signs `p : ℕ → ℕ`, given by the conditions
`χ_l(x) = χ_l(sgn x) |x|^{e_l}`, `χ_l(1) = 1` and `χ_l(−1) = (−1)^{p_l}`, with
`BlockOrdered ks e`. Let `W` be a proper subspace of the `O(n)`-finite functions of
`principalSeries ℝ n χ` (`n = dim ks`; some `O(n)`-finite function of the principal series is not
in `W`), stable under right translation by `O(n)` and under right derivatives. Then
`jac ks e p w = 0` for every `w ∈ W`.

It is proved as `Langlands.Archimedean.realBlockFunctional`, from `jac_eq_zero_of_proper`. The
condition `‖χ_l(−1)‖ = 1` of `IsSignedPower` follows from `χ_l(−1) = (−1)^{p_l}`.

Provenance. Derived, internal infrastructure: the Jacquet-integral form of the Langlands lemma
for a parabolic subgroup with tempered-up-to-twist blocks. No literature statement is claimed.

## Proof

### Characters

* `BlockOrdered.shift`: `BlockOrdered` is invariant under `e ↦ e − c`.
* `isSignedPower_blockDualChar`, `blockDualChar_neg_one`: `RealBlockDual.blockDualChar a χ` is
  signed-power with exponents `−(e_{a+l} + a/2)` and signs `p_{a+l}` (since
  `((−1)^{p})⁻¹ = (−1)^{p}`).
* `blockShiftChar_neg_one`: `RealBlockJacquet.blockShiftChar k χ` has the same signs `p`; it is
  signed-power with exponents `e − (k+1)/2` by `RealBlockJacquet.isSignedPower_blockShift`.

### Linearity

* `blockPair_smul`: `blockPair φ (c • f) = c • blockPair φ f`.
* `blockPair_add`: on `O(a+k+1)`-finite principal-series functions, `blockPair φ` is additive. Both
  sides lie in the principal series of `GL_a(ℝ)` (`blockPair_mem`), agree on `O(a)` by the
  linearity of `blockPairOn`, and so are equal by the Library's
  `eq_of_eqOn_unitaryCompact_of_mem_principalSeries`.
* `jac_cons` (definitional unfolding), `jac_smul`, and `jac_add` (by induction on `ks`).
* `jacKernel`: the submodule of `O(n)`-finite principal-series functions on which `jac` vanishes.

### Vanishing on annihilators

`jac_eq_zero` (by induction on `ks`): let `U ≠ 0` be a `(𝔤, K)`-stable space of `O(n)`-finite
functions of the principal series of `χ⁻¹`, and `h` an `O(n)`-finite function of the principal
series of `χ` with `∫_{O(n)} u h = 0` for all `u ∈ U`. Then `jac ks e p h = 0`.

* `ks = []`: `GL_0(ℝ)` is trivial, and `∫ u h = u(1) h(1)` (probability measure) with
  `u(1) ≠ 0` for some `u ∈ U`.
* `ks = k :: ks'`, `a = dim ks'`:
  1. `TiedIrreducible`, applied to `blockDualChar a χ` (the exponents are tied by
     `IsBlockDominant.tie`), gives the irreducibility needed by
     `RealBlockDual.integral_restrictBlock_mul_blockPair_eq_zero` with `φ = blockVector a k e p`.
     This yields `∫_{O(a)} u'(κ) blockPair φ h (κ) dκ = 0` for all `u'` in
     `U' = U.map restrictBlock`.
  2. `RealBlockDual.map_restrictBlock` shows that `U'` is a nonzero `(𝔤_a, O(a))`-stable space of
     the principal series of `(blockShiftChar k χ)⁻¹`.
  3. `RealBlockJacquet.blockPair_mem` shows that `blockPair φ h` lies in the principal series of
     `blockShiftChar k χ`.
  4. The induction hypothesis on `GL_a(ℝ)`, with exponents `e − (k+1)/2` and the same signs,
     finishes the step.

### Proper submodules

`jac_eq_zero_of_proper`: a proper `(𝔤, K)`-stable `W` has a nonzero `(𝔤, K)`-stable annihilator
in the dual principal series, by the Library's `JacquetKernel.annihilator` and its lemmas
`annihilator_le`, `annihilator_rightTranslation`, `annihilator_rightDerivative` and
`annihilator_ne_bot`. Applying `jac_eq_zero` to that annihilator gives `W ≤ jacKernel`.

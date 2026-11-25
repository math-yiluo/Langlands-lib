# The block Jacquet functional and its vanishing on proper submodules

Lean module: `Langlands.Representation.Archimedean.ComplexBlockFunctional`.

This module is infrastructure for the proof of
`ComplexStandardLanglandsQuotientStatement`. It generalizes the published `ComplexJacquetDual` and
`ComplexJacquetKernel` (strictly decreasing exponents, one row at a time) to block decompositions
in which the exponents are tied within each block and strictly decrease between blocks. It assembles
the recursion from `ComplexBlockJacquet` (the function `blockPair`) and `ComplexBlockDual` (the dual
step).

Notation: `GL_N(ℂ)` is `Langlands.GeneralLinear N ℂ` and `U(N)` is `unitaryCompact ℂ N` with Haar
probability measure `unitaryHaar N`. `IsPhasePower χ e` (`ComplexPartialJacquet`) means
`χ_l(z) = χ_l(z/|z|)(|z|²)^{e_l}`, `χ_l(1) = 1` and `|χ_l| = 1` on the unit circle.
`phaseUnit z = z/|z|` (`ComplexGramFormula`). `phaseVector n e p a`
(`ComplexJacquetNonvanishing`) is the principal-series function whose restriction to `U(n)` is the
phase monomial `κ ↦ ∏_l κ_ll^{p⁺_l + a_l} conj(κ_ll)^{p⁻_l + a_l}`. Unprefixed names below are in
the namespace `Langlands.Archimedean.ComplexBlockFunctional`.

## Definitions

* `dim ks`: for a list `ks` of block parameters (block sizes `k + 1`, the last block first),
  `dim [] = 0` and `dim (k :: ks) = dim ks + (k + 1)`.
* `BlockOrdered ks e`: for `ks = k :: ks'`, `IsBlockDominant e (dim ks') k` holds (the exponents at
  positions `dim ks', …, dim ks' + k` have equal real parts; the real parts decrease weakly before
  position `dim ks'` and strictly at that position), and recursively `BlockOrdered ks' e`.
  `BlockOrdered [] e` is `True`.
* `TiedIrreducible`: for every `b`, every phase-power `ψ` with exponents `f`, integral phase weights
  `q` (`ψ_l(u) = u^{q_l}` on the unit circle) and `Re f_l = Re f_0` for `l < b`, the
  `(𝔤𝔩_b(ℂ), U(b))`-module `(principalSeriesRep ℂ b ψ, principalSeriesLie ℂ b ψ)` is irreducible.
  The Library's `ComplexTemperedStandardIrreducibleStatement` is the corresponding statement for
  complex standard modules.
* `blockVector a k e p = phaseVector (k+1) (l ↦ −(e_{a+l} + a/2)) (l ↦ −p_{a+l}) 0`: a phase vector
  of the dual principal series of the block at positions `a, …, a+k` (`blockVector_mem`).
* `jac ks e p h` (the block Jacquet functional): `jac [] e p h = h(1)` and
  `jac (k :: ks) e p h = jac ks (e − (k+1)/2) p (blockPair (blockVector (dim ks) k e p) h)`.

## The statement

`ComplexBlockFunctionalStatement` assumes three statements: `ComplexBlockChartIntegrableStatement`,
`ComplexBlockParabolicIntegrationStatement` and `TiedIrreducible`. None of them is proved here.
Under these assumptions it says the following.

Let `χ` be phase-power characters with exponents `e`, given by the conditions `χ_l(z) =
χ_l(z/|z|)(|z|²)^{e_l}` and `χ_l(1) = 1`, with `χ_l(u) = u^{p_l}` on the unit circle, and with
`BlockOrdered ks e`. Let `W` be a proper subspace of the `U(n)`-finite functions of
`principalSeries ℂ n χ` (`n = dim ks`; some `U(n)`-finite function of the principal series is not
in `W`), stable under right translation by `U(n)` and under right derivatives. Then
`jac ks e p w = 0` for every `w ∈ W`.

It is proved as `Langlands.Archimedean.complexBlockFunctional`, from `jac_eq_zero_of_proper`.

Provenance. Derived, internal infrastructure: the Jacquet-integral form of the Langlands lemma
for a parabolic subgroup with tempered-up-to-twist blocks. No literature statement is claimed.

## Proof

### Characters

* `BlockOrdered.shift`: `BlockOrdered` is invariant under `e ↦ e − c`.
* `isPhasePower_blockDualChar`, `blockDualChar_phase`: `ComplexBlockDual.blockDualChar a χ` is
  phase-power with exponents `−(e_{a+l} + a/2)` and weights `−p_{a+l}`.
* `blockShiftChar_phase`: `ComplexBlockJacquet.blockShiftChar k χ` has the same weights `p`.

### Linearity

* `blockPair_smul`: `blockPair φ (c • f) = c • blockPair φ f`.
* `blockPair_add`: on `U(a+k+1)`-finite principal-series functions, `blockPair φ` is additive. Both
  sides lie in the principal series of `GL_a(ℂ)` (`blockPair_mem`), agree on `U(a)` by the
  linearity of `blockPairOn`, and so are equal by `eq_of_eqOn_unitary`.
* `jac_cons` (definitional unfolding), `jac_smul`, and `jac_add` (by induction on `ks`).
* `jacKernel`: the submodule of `U(n)`-finite principal-series functions on which `jac` vanishes.

### Vanishing on annihilators

`jac_eq_zero` (by induction on `ks`): let `U ≠ 0` be a `(𝔤, K)`-stable space of `U(n)`-finite
functions of the principal series of `χ⁻¹`, and `h` a `U(n)`-finite function of the principal
series of `χ` with `∫_{U(n)} u h = 0` for all `u ∈ U`. Then `jac ks e p h = 0`.

* `ks = []`: `GL_0(ℂ)` is trivial, and `∫ u h = u(1) h(1)` with `u(1) ≠ 0` for some `u ∈ U`.
* `ks = k :: ks'`, `a = dim ks'`:
  1. `TiedIrreducible`, applied to `blockDualChar a χ` (the exponents are tied by
     `IsBlockDominant.tie`), gives the irreducibility needed by
     `ComplexBlockDual.integral_restrictBlock_mul_blockPair_eq_zero` with
     `φ = blockVector a k e p`. This yields `∫_{U(a)} u'(κ) blockPair φ h (κ) dκ = 0` for all `u'`
     in `U' = U.map restrictBlock`.
  2. `ComplexBlockDual.map_restrictBlock` shows that `U'` is a nonzero `(𝔤_a, U(a))`-stable space
     of the principal series of `(blockShiftChar k χ)⁻¹`.
  3. `ComplexBlockJacquet.blockPair_mem` shows that `blockPair φ h` lies in the principal series
     of `blockShiftChar k χ`.
  4. The induction hypothesis on `GL_a(ℂ)`, with exponents `e − (k+1)/2`, finishes the step.

### Proper submodules

`jac_eq_zero_of_proper`: a proper `(𝔤, K)`-stable `W` has a nonzero `(𝔤, K)`-stable annihilator
in the dual principal series, by the Library's `ComplexJacquetKernel.annihilator` and its lemmas
`annihilator_le`, `annihilator_rightTranslation`, `annihilator_rightDerivative` and
`annihilator_ne_bot`. Applying `jac_eq_zero` to that annihilator gives `W ≤ jacKernel`.

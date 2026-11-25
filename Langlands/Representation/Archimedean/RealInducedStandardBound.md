# The torus-pairing bound for real standard modules

Lean module: `Langlands.Representation.Archimedean.RealInducedStandardBound`.

This module is part of the proof
of `RealStandardLanglandsQuotientStatement` (module `RealLargeLanglandsQuotientReduction`). It
applies the general torus-pairing bound `RealInducedTorusBoundStatement` (module
`RealInducedTorusBound`) to an `O(N)`-finite function `h` of a real standard module and an
`O(N)`-finite function `u` of the dual principal series. It states the result as
`RealInducedStandardBoundStatement` and proves it (`realInducedStandardBound`). Unprefixed names
below are in the namespace `Langlands.Archimedean.RealInducedStandardBound`.

Provenance: derived. This is internal analytic infrastructure for the proof of
`RealStandardLanglandsQuotientStatement`. No statement in the literature is claimed. The module
only checks the hypotheses of `RealInducedTorusBoundStatement` for standard modules.

## Notation

`GL_N(ℝ)` is `Langlands.GeneralLinear N ℝ` and `O(N)` is the Library's `unitaryCompact ℝ N`.
Smooth means `ContMDiff (matrixModel ℝ N) 𝓘(ℝ, ℂ) ∞`. The Library supplies the following, in
`StandardModule`, `PrincipalSeriesGramFormula`, `PartialJacquetIntegral` and
`RealStrictCharacterLanglandsQuotient`:

* `realPositionCharacter ds l`: the character at the diagonal position `l` of the list of real
  blocks `ds`. An induction block `d` (weight `m`, exponent `t`) at the positions `p, p + 1` has
  `sgn^{|m|+1} |·|^{t+|m|/2}` at `p` and `|·|^{t−|m|/2}` at `p + 1`.
* `realPositionExponent ds l`: the exponent of `|·|` in that character.
* `realInducedBlockAt ds p`: the induction block whose first position is `p`, if there is one.
* `realStandardModule N ds`: the functions `f` in `principalSeries ℝ N (realPositionCharacter ds)`
  such that, for every induction block `d` at `p`, the block Fourier coefficients
  `blockFourierCoefficient N p k f` vanish for `|k| < |d.weight|`.
* `dualChar χ l x = (χ l x)⁻¹`.
* `isSignedPower ds`: `realPositionCharacter ds` is a signed power with exponents
  `realPositionExponent ds`.
* `shiftedExponent N e l = e_l + (N − 1)/2 − l`.
* `PrincipalSeriesExtension.extension s φ`: the Gram-formula extension of a function `φ` on
  `O(N)`. Its value at `b κ` (`b` upper triangular, `κ ∈ O(N)`) is `∏_l |b_ll|^{s_l} · φ(±κ)`.

The modules `RealInducedBlockBound`, `RealInducedTorusCore` and `RealInducedTorusBound` supply the
following:

* `Slot N`: a block `p, p + 1` with an exponent `α`, a weight `M`, a mode `j` and coordinates
  `x, y, w`.
* `Slot.Disjoint`, `coeffs`, `IsKFin`, `IsMode`, `InClass`, `HasDegree` and `zeroModes`.
* `coeffs (zeroModes S) F 1`: the iterated mode-`0` rotation integral
  `∫ F(r_{p_1}(θ_1) ⋯ r_{p_r}(θ_r)) dθ`, that is, the integral over the torus `T` of the rotations
  of the blocks of `S`.

## Statement

`RealInducedStandardBoundStatement` reads: for all `N`, every list of real blocks `ds` with
`realRank ds = N`, every `u` in `kFiniteFunctions (principalSeries ℝ N (dualChar
(realPositionCharacter ds))) (unitaryCompact ℝ N)` and every `h` in `kFiniteFunctions
(realStandardModule N ds) (unitaryCompact ℝ N)`, there is a real `C` with

`‖coeffs (zeroModes (slots ds N)) (x ↦ u(x y_1) h(x y_2)) 1‖ ≤
C · ‖coeffs (zeroModes (slots ds N)) (x ↦ expFun N (−t) (x y_1) · expFun N t (x y_2)) 1‖`

for all `y_1, y_2 ∈ GL_N(ℝ)`. Here `t = realPositionBlockExponent ds`. So the torus average of
`u(τ y_1) h(τ y_2)` over the rotations of the induction blocks is bounded, uniformly in the two
points, by the torus average of the product of the right `O(N)`-invariant comparison functions
`E_u = expFun N (−t)` and `E_h = expFun N t`.

## Definitions

* `realPositionBlockExponent ds l`: the real part of the exponent of the block containing the
  position `l`. For a character block this is `Re t`. For both positions of an induction block of
  exponent `t` it is `Re t`. Past the end it is `0`.
* `mkSlot ds N p hp d`: the slot at the block `p, p + 1`. Its exponent is
  `α = realPositionExponent ds p + (N − 1)/2 − p`, its weight is `M = |d.weight|`, and its mode
  and coordinates are `0`.
* `slotAt ds N p`: `some (mkSlot ds N p hp d)` if `realInducedBlockAt ds p = some d` and
  `p + 1 < N`, and `none` otherwise.
* `slots ds N`: the list of `slotAt ds N p` for `p < N`, in increasing order of `p`. These are
  the slots of all induction blocks.
* `absChar e l x = |x|^{e_l}` for a real exponent function `e : ℕ → ℝ`.
* `expFun N e = extension (shiftedExponent N e) 1`. This is the right `O(N)`-invariant function
  `b κ ↦ ∏_l |b_ll|^{e_l + (N − 1)/2 − l}` of the principal series of `absChar e`.
* `shiftExp N e i = e_i + (N − 1)/2 − i` and `shiftExpRe N t i = t_i + (N − 1)/2 − i`: the
  exponents of exponential equivariance, complex and real.

## Results

Positions of the blocks.

* `induced_at`: suppose `realInducedBlockAt ds p = some d`. Then the following hold:
  * the characters at `p` and `p + 1` are `realInducedFirstCharacter d` and
    `realInducedSecondCharacter d`;
  * the exponents there are `d.exponent ± |d.weight|/2`;
  * both block exponents are `Re d.exponent`;
  * `realInducedBlockAt ds (p + 1) = none`.
* `exponent_re_eq`: at a position `i` that is neither `p` nor `p + 1` for an induction block at
  `p`, `Re (realPositionExponent ds i) = realPositionBlockExponent ds i`.

Slots.

* `mem_slotAt`, `mem_slots`: every slot of `slots ds N` is `mkSlot ds N p hp d` for an induction
  block `d` at `p`.
* `mkSlot_mem_slots`: conversely, every such `mkSlot` lies in `slots ds N`.
* `pairwise_slots`: the slots of `slots ds N` are pairwise disjoint. Two induction blocks with
  first positions `a < b` satisfy `a + 1 < b`, because `realInducedBlockAt ds (a + 1) = none`.

Degrees.

* `hasDegree_mono`: `HasDegree S D f` and `D ≤ D'` imply `HasDegree S D' f`.
* `exists_hasDegree`: a continuous right `O(N)`-finite function has some degree `D` along any
  list of slots. The proof is an induction over the list, using the Library's
  `exists_blockFourierCoefficient_eq_zero` at each slot.

Exponential equivariance.

* `apply_exp`: for a signed power `χ` with exponents `e`, `χ_l(e^x) = exp(e_l x)`.
* `isExpEquivariant_of_mem`: every function of `principalSeries ℝ N χ`, for a signed power `χ`
  with exponents `e`, is `IsExpEquivariant (shiftExp N e)`. This is the Library's
  `isExpEquivariant_of_mem_principalSeries`.

Comparison functions.

* `absChar_signUnit`, `absChar_eq`, `principalSeriesCharacter_absChar_sign`: `absChar e` is
  trivial on signs and has the form required by the extension machinery.
* `expFun_mem`: `expFun N e ∈ principalSeries ℝ N (absChar e)`. The proof applies
  `extension_mem_principalSeries` with `φ = 1`.
* `contMDiff_expFun`: `expFun N e` is smooth.
* `isExpEquivariant_expFun`: `expFun N e` is `IsExpEquivariant` with the real exponents
  `e_i + (N − 1)/2 − i`.
* `expFun_mul`: `expFun N e (g k) = expFun N e g` for `k ∈ O(N)`. The proof uses
  `rightTranslation_extension`.
* `expFun_one`: `expFun N e 1 = 1`. The proof uses `extension_unitary`.

Modes.

* `not_isMode`: if `j` is not of the form `±(M + 1 + 2l)` with `l ∈ ℕ`, then either `|j| < M` or
  `(−1)^j ≠ (−1)^{M+1}`.

Standard modules lie in the class.

* `inClass_slots`: suppose `h` is an `O(N)`-finite function of `realStandardModule N ds` and
  `HasDegree (slots ds N) D h`. Then `InClass (slots ds N) D h`. The proof checks two conditions
  at the slot of an induction block `d` at `p`.
  * Block covariance with exponents `(α, α − (|m| + 1))` follows from
    `isBlockCovariant_of_isExpEquivariant`. The exponents at `p` and `p + 1` differ by `|m|`, and
    the shift `(N − 1)/2 − l` contributes `1` more.
  * Every non-allowed mode vanishes. If `|j| < |m|`, this is the defining condition of the
    standard module. If `j` has the wrong parity, it follows from the Library's
    `blockFourierCoefficient_eq_zero_of_parity`, because the product of the two characters at
    `−1` is `(−1)^{|m|+1}`.

The bound.

* `exists_bound`: the inequality of the statement for given `ds`, `u`, `h`. The proof applies
  `norm_coeffs_le_mul_norm_coeffs` (module `RealInducedTorusBound`) with:
  * the degree `max D_u D_h`;
  * `α_u = shiftExp N (−e)` and `α_h = shiftExp N e`, where `e = realPositionExponent ds`;
  * `σ_u = shiftExpRe N (−t)` and `σ_h = shiftExpRe N t`;
  * `E_u = expFun N (−t)` and `E_h = expFun N t`.

  The exponent hypotheses are then direct computations at each slot:
  * the differences of `α_u + α_h` and of `σ_u + σ_h` across a block are both `2`;
  * `Re (α_u + α_h)_p = (σ_u + σ_h)_p`;
  * `σ_{h,p+1} = σ_{h,p} − 1`;
  * `σ_{h,p} = Re α − |m|/2`.

  Away from the blocks, `Re α = σ` follows from `exponent_re_eq`.
* `realInducedStandardBound : RealInducedStandardBoundStatement` is `exists_bound`.

# The unlinked swap of two induction blocks

Lean module: `Langlands.Representation.Archimedean.RealInducedSwapUnlinked`.

Main theorem: `Langlands.Archimedean.realInducedSwap : RealInducedSwapStatement`. It proves the
Library statement `Langlands.Archimedean.RealInducedSwapStatement` of
`Langlands.Representation.Archimedean.RealUnlinkedSwapReduction` (Task 7172). For lists `pre`,
`post` of real blocks and complex characters `d`, `e` of nonzero weights with
`Re t(e) ≤ Re t(d)` whose Mœglin data are not linked, of total rank `n`, there is an injective
`(𝔤, K)`-intertwiner from the `O(n)`-finite functions of the standard module of
`pre ++ [induced d, induced e] ++ post` to those of `pre ++ [induced e, induced d] ++ post`. The
helper results are in namespace `Langlands.Archimedean.RealInducedSwapUnlinked`.

This module only assembles results. The analytic and arithmetic work is in the modules listed
under Dependencies. The proof is internal to this project. The route deforms the four rank-one
crossings and takes a limit at the central parameter. It follows the plan of the co-executor
Worker 772 and does not formalize a literature argument.

## Proof

1. **Reduction to rank 4.** `RealInducedSwapIntegralReduction.realInducedSwap_iff_integral`
   (Library) states `RealInducedSwapStatement ↔ IntegralSwapStatement`. The Lean proof applies its
   reverse direction. `IntegralSwapStatement` asks for an injective intertwiner
   `RealInjectiveIntertwinerExists 4 (source d e) (target d e)`, from
   `[induced d, induced e]` to `[induced e, induced d]`, whenever `d`, `e` have nonzero weights
   with different absolute values and `IntegralWindow d e m` holds for some `m : ℕ`. The window
   means `min |d.weight| |e.weight| ≤ m`, `2m ≤ |d.weight| + |e.weight|` and
   `(chB d).exponent - (chA e).exponent = -m`. The generic and equal-weight cases, and the
   surrounding blocks `pre` and `post`, are handled inside that Library reduction.

2. **Equal imaginary parts** (`im_eq_of_integralWindow`). Here
   `(chB d).exponent = d.exponent - |d.weight|/2` and `(chA e).exponent = e.exponent + |e.weight|/2`
   (`chB_exponent`, `chA_exponent`). Taking imaginary parts of the third window condition gives
   `d.exponent.im - e.exponent.im = 0`.

3. **Balanced normalizations give the swap** (`swap_of_balanced`). Let `a` and `b` be
   normalizations (`RealInducedSwapBalanced.Normalization`) with `IsValid d e a`, `IsValid e d b` and
   `Balanced a b`, and assume `d.exponent.im = e.exponent.im`.
   * `RealInducedSwapLimit.hasGenericPath_of_im_eq` gives a nontrivial filter `L ≤ 𝓝 0` along
     which eventually `z ≠ 0` and `IsGenericShift d e z`.
   * Let `S = RealInducedSwapBalanced.targetFamily d e a ha`. For every input `f`,
     `z ↦ S z f` is weakly analytic at `0` (`targetFamily_analytic`).
   * For `z ≠ 0` with `hg : IsGenericShift d e z`, `targetFamily_eq_generic` gives
     `S z = scalar a z • shiftedMap d e (genericFourCrossings hg)`.
   * `S 0` is injective (`targetFamily_zero_injective`, which uses `b`, `hb`, `Balanced a b` and the
     same path).
   * `RealInducedSwapScalarLimit.realInjectiveIntertwinerExists_of_weaklyAnalytic_smul`
     then shows that `S 0` is an intertwiner. With injectivity this gives
     `RealInjectiveIntertwinerExists 4 (source d e) (target d e)`.

4. **Abstract assembly** (`integralSwap_of_exists_balanced`). Suppose every case of
   `IntegralSwapStatement` has normalizations `a`, `b` as in step 3. Steps 2 and 3 then give
   `IntegralSwapStatement`.

5. **Arithmetic input.** `RealInducedSwapIntegralNormalization.exists_balanced_of_integralWindow`
   (Worker 772) provides, from `d.weight ≠ 0`, `e.weight ≠ 0`,
   `|d.weight| ≠ |e.weight|` and `IntegralWindow d e m`, normalizations `a`, `b` with
   `IsValid d e a`, `IsValid e d b` and `Balanced a b`. So the hypothesis of step 4 holds, and
   `realInducedSwap` follows from step 1.

## Results

* `im_eq_of_integralWindow {d e} {m} (hw : IntegralWindow d e m) : d.exponent.im = e.exponent.im`.
* `swap_of_balanced d e a b (ha : IsValid d e a) (hb : IsValid e d b) (hab : Balanced a b)
  (him : d.exponent.im = e.exponent.im) : RealInjectiveIntertwinerExists 4 (source d e) (target d e)`.
* `integralSwap_of_exists_balanced (h : ∀ d e, d.weight ≠ 0 → e.weight ≠ 0 →
  d.weight.natAbs ≠ e.weight.natAbs → ∀ m, IntegralWindow d e m →
  ∃ a b, IsValid d e a ∧ IsValid e d b ∧ Balanced a b) : IntegralSwapStatement`.
* `Langlands.Archimedean.realInducedSwap : RealInducedSwapStatement`.

## Dependencies

* Library: `RealUnlinkedSwapReduction` (the target statement), `RealInducedSwapIntegralReduction`,
  `RealInducedSwapShifted`, `RealInducedSwapGeneric`, `RealInducedSwapInverse`,
  `RealCharacterInducedSwap`.
* Helper module of this candidate: `RealInducedSwapScalarLimit`. It extends the limit theorem to
  scalar multiples of shifted maps.
* Separately submitted units: `RealExponentDeformation` and `RealInducedSwapLieLimit` (Worker
  5546), and `RealFiniteLayerRegularization`, `RealInducedSwapRegularizedFamily`,
  `RealInducedSwapRegularization`, `RealInducedSwapGerm`, `RealInducedSwapLimit`,
  `RealInducedSwapBalanced` and `RealInducedSwapIntegralNormalization` (Worker 772).

Axioms of `realInducedSwap`: `propext`, `Classical.choice`, `Quot.sound`.

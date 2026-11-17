# Lie equivariance of limits of shifted four-crossing maps

Lean module: `Langlands.Representation.Archimedean.RealInducedSwapLieLimit`, namespace
`Langlands.Archimedean.RealInducedSwapLieLimit`.

## Purpose and provenance

This is internal infrastructure for the deformation route to
`Langlands.Archimedean.RealInducedSwapStatement` (Task 7172). The route deforms the four
rank-one crossings of `RealInducedSwapShifted` by a common shift `z` of their recurrence
parameters and takes a limit at `z = 0`. A shifted map `shiftedMap d e h` with
`h : FourCrossings d e z` goes between the fixed modules of `[induced d, induced e]` and
`[induced e, induced d]`. Away from zero, no Lie-intertwining property for the fixed exponents is
required. Instead, the shifted map is the honest zero-shift map for a first block whose exponent is
moved by `z`, read in the compact picture on `O(4)`. The limit theorem of `RealExponentDeformation`
(`isRealStandardIntertwiner_of_tendsto`) then gives an intertwiner at `0`.

The module only connects `RealInducedSwapShifted` to `RealExponentDeformation`; it formalizes no
literature statement. The underlying fact is the standard compact picture of principal series:
restriction to `O(n)` does not depend on the exponents.

## Definitions

* `moved d z`: the complex character data `characterOfParams d.weight (d.exponent + z)`, i.e.
  `(w/|w|)^m |w|^{2(t+z)}` when `d` is `(w/|w|)^m |w|^{2t}`. `moved_weight` and
  `moved_exponent` record that its weight is `d.weight` and its exponent is `d.exponent + z`
  (both by `rfl`).
* `crossingAtZero h hp he`: given a `Crossing x y z` (a sequence `μ`, symmetric for the parity
  and sign of the pair `y, x`, and recurrent with parameter `x.exponent - y.exponent + 1 + z`)
  and a real character `x'` with `x'.parity = x.parity` and `x'.exponent = x.exponent + z`,
  the same sequence `μ` as a `Crossing x' y 0`. The pair parity and the sign `sigma0` only see
  the parities, and the recurrence parameter `x'.exponent - y.exponent + 1 + 0` equals the
  original one.
* `atZero d e h`: for `h : FourCrossings d e z`, the four crossings `bc, ac, bd, ad` with the same
  four sequences, as `FourCrossings (moved d z) e 0`. In all four crossings the first character
  is a position character `chA d` or `chB d` of `d`. The position characters of `moved d z` have
  the same parities and exponents moved by `z` (`chA_exponent`, `chB_exponent`).

## Results

* `shiftedMap_eqOn`: for `h : FourCrossings d e z`, `f` in the `O(4)`-finite part of the source
  module of `d, e` and `f'` in that of `moved d z, e`, if `f'` and `f` agree on `O(4)` then
  `shiftedMap (moved d z) e (atZero d e h) f'` and `shiftedMap d e h f` agree on `O(4)`.
  *Proof.* Both maps are the inclusion into the expanded four-character module followed by the
  four block multiplier maps `dataBC`, `dataAC`, `dataBD`, `dataAD`. Corresponding steps use the
  same position and the same sequence. `RealExponentDeformation.blockFrobMap_eqOn` is applied
  four times.
* `isExponentShift_source`, `isExponentShift_target`: `[induced (moved d z), induced e]` is the
  exponent shift (`IsExponentShift`) of `[induced d, induced e]` by `z • ![1, 1, 0, 0]`, and
  `[induced e, induced (moved d z)]` that of `[induced e, induced d]` by `z • ![0, 0, 1, 1]`.
  *Proof.* `IsExponentShift.of_forall₂`: the blocks have the same weights, and the position
  exponents `t ± |m|/2` of an induction block move with `t`. The four positions are checked by
  `fin_cases` and `simp`.
* `isRealStandardIntertwiner_atZero`: `shiftedMap (moved d z) e (atZero d e h)` is an
  intertwiner (`IsRealStandardIntertwiner`) from the source to the target module of
  `moved d z, e`. *Proof.* `shiftedMap_zero_modulo` (zero shift intertwines modulo `⊥`) and
  `isRealStandardIntertwiner_of_modulo_bot`.
* `isRealStandardIntertwiner_of_tendsto_shifted`: take a nontrivial filter `L ≤ 𝓝 0` and linear
  maps `S z` from the `O(4)`-finite source module of `d, e` to the target module. Assume that for
  every `f` and every linear functional `ℓ`, `ℓ (S z f)` tends to `ℓ (S 0 f)` along `L`. Assume
  also that for `z` eventually in `L`, `z ≠ 0` and `S z = shiftedMap d e h` for some
  `h : FourCrossings d e z`. Then `S 0` is an intertwiner from `[induced d, induced e]` to
  `[induced e, induced d]`. *Proof.* `isRealStandardIntertwiner_of_tendsto` with
  `ds' z = source (moved d z) e`, `es' z = target (moved d z) e`, `a = ![1, 1, 0, 0]`,
  `b = ![0, 0, 1, 1]` and `T = shiftedMap (moved d z) e (atZero d e h)`. Its hypotheses are the
  three results above.
* `isRealStandardIntertwiner_of_weaklyAnalytic`: the same conclusion when instead every
  `z ↦ S z f` is weakly analytic at `0` (`RealBlockMultiplierAnalytic.IsWeaklyAnalyticAt`: every
  scalar coordinate `ℓ (S z f)` is analytic at `0`). Analytic functions are continuous, so
  `ℓ (S z f) → ℓ (S 0 f)` along `𝓝 0`, hence along `L`.
* `realInjectiveIntertwinerExists_of_weaklyAnalytic`: if moreover `S 0` is injective, then
  `RealInjectiveIntertwinerExists 4 [induced d, induced e] [induced e, induced d]`, witnessed by
  `S 0`.

## Dependencies

Library modules `RealInducedSwapShifted`, `RealBlockMultiplierAnalytic` and
`ComplexJacquetBorel` (for `characterOfParams`), and `RealExponentDeformation` (candidate
ce8243b1, submitted for the same task). Axioms: `propext`, `Classical.choice`, `Quot.sound`.

`moved d z` abbreviates the existing `ComplexBlock.twist z d`.

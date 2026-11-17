# Limits of scalar multiples of shifted four-crossing maps

Lean module: `Langlands.Representation.Archimedean.RealInducedSwapScalarLimit`, namespace
`Langlands.Archimedean.RealInducedSwapScalarLimit`.

## Purpose and provenance

This is internal infrastructure for the proof of `Langlands.Archimedean.RealInducedSwapStatement`
(Task 7172). The normalized families of `RealInducedSwapBalanced`
(`targetFamily d e a ha`) need not equal the shifted maps `shiftedMap d e h` of
`RealInducedSwapShifted` at generic nonzero shifts `z`. Instead, they equal scalar multiples
`scalar a z • shiftedMap d e h`, where `scalar a z = z ^ totalOrder a.choices / z ^ divisionOrder a`. This module extends the limit
theorem of `RealInducedSwapLieLimit` from `S z = shiftedMap d e h` to `S z = c • shiftedMap d e h`.
It formalizes no literature statement.

## Results

* `isRealStandardIntertwiner_smul`: if `B` is an intertwiner (`IsRealStandardIntertwiner n ρ π ds B`)
  from the `O(n)`-finite part of the standard module of `ds` into `(ρ, π)`, then so is `c • B` for
  every `c : ℂ`. *Proof.* Both clauses of the definition give membership of the translated or
  differentiated function and an identity `B ⟨_, hf⟩ = ρ(k) (B f)` (resp. `π (1 ⊗ X) (B f)`).
  Multiply by `c` and use linearity of `ρ(k)` and `π (1 ⊗ X)`.
* `isRealStandardIntertwiner_of_tendsto_smul`: let `L` be a nontrivial filter with `L ≤ 𝓝 0` and
  `S z` linear maps from the `O(4)`-finite part of the module of `[induced d, induced e]` to that of
  `[induced e, induced d]`. Assume `ℓ (S z f) → ℓ (S 0 f)` along `L` for every `f` and every linear
  functional `ℓ`. Assume also that for `z` eventually in `L`, `z ≠ 0` and `S z = c • shiftedMap d e h`
  for some `c : ℂ` and `h : FourCrossings d e z`. Then `S 0` is an intertwiner from
  `[induced d, induced e]` to `[induced e, induced d]`. *Proof.* This is
  `RealExponentDeformation.isRealStandardIntertwiner_of_tendsto` with `ds' z = source (moved d z) e`,
  `es' z = target (moved d z) e`, `a = ![1, 1, 0, 0]`, `b = ![0, 0, 1, 1]`. The intertwiner is
  `T = c • shiftedMap (moved d z) e (atZero d e h)`. It is an intertwiner by
  `isRealStandardIntertwiner_atZero` and `isRealStandardIntertwiner_smul`. On `O(4)` it agrees with
  `S z f = c • shiftedMap d e h f` by `shiftedMap_eqOn`, multiplied by `c`. The exponent shifts are
  `isExponentShift_source` and `isExponentShift_target`.
* `isRealStandardIntertwiner_of_weaklyAnalytic_smul`: the same conclusion when every `z ↦ S z f` is
  weakly analytic at `0` (`RealBlockMultiplierAnalytic.IsWeaklyAnalyticAt`). Analytic scalar
  coordinates are continuous at `0`, hence converge along `L ≤ 𝓝 0`.
* `realInjectiveIntertwinerExists_of_weaklyAnalytic_smul`: if moreover `S 0` is injective, then
  `RealInjectiveIntertwinerExists 4 [induced d, induced e] [induced e, induced d]`, witnessed by
  `S 0`.

## Dependencies

`RealInducedSwapLieLimit` (and through it `RealExponentDeformation`, `RealInducedSwapShifted`,
`RealBlockMultiplierAnalytic`). Axioms: `propext`, `Classical.choice`, `Quot.sound`.

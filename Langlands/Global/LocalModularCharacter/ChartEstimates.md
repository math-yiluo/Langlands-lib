# Modular-character bounds from derivatives in a chart at the identity

Module `Langlands.Global.LocalModularCharacter.ChartEstimates`.

This module turns two differentiability facts about a chart at the identity into an upper bound
for the modular character. It combines the chart comparison `modularCharacter_le_of_chart`
(module `ChartComparison`) with the estimates in normed spaces from module `LocalScaling`.

The group `H` is a topological group. From `modularCharacter_le_of_chart_ultrametric` onward it
is also locally compact, Hausdorff and second countable, with its Borel σ-algebra. The model
space `E` is a normed additive group, and `φ : H → E` is an open partial homeomorphism. The
field `K` is a nontrivially normed field and `E` is a normed `K`-space. In the statements below,
`φ⁻¹` denotes Lean's total function `φ.symm`.

## Results on the group law in the chart

Assume `1 ∈ φ.source` and `φ 1 = 0`.

- `chart_symm_zero`: `φ⁻¹ 0 = 1`.
- `tendsto_chart_symm_zero`: `φ⁻¹` tends to `1` at `0`.
- `chart_mul_zero_eventually`: for `y` near `0`, `φ (φ⁻¹ y · φ⁻¹ 0) = y`.
- `tendsto_chart_inv`: the inverse read in the chart, `y ↦ φ ((φ⁻¹ y)⁻¹)`, tends to `0` at `0`.
- `chart_inv_mul_eventually`: write `m y z = φ (φ⁻¹ y · φ⁻¹ z)` and `ι y = φ ((φ⁻¹ y)⁻¹)`. For
  `(y, z)` near `(0, 0)`, `m (ι y) (m y z) = z`.
- `chart_mul_inv_eventually`: for `(y, z)` near `(0, 0)`, `m y (m (ι y) z) = z`.
- `chart_conj_zero`: for every `g ∈ H`, `φ (g · φ⁻¹ 0 · g⁻¹) = 0`.

## Results on left translations

Let `λ` be an additive Haar measure on `E` (`l` in Lean). Assume `L : E × E → E` is a continuous
`K`-linear map, and that `(y, z) ↦ φ (φ⁻¹ y · φ⁻¹ z)` has strict derivative `L` at `(0, 0)`. Also
assume `L (0, w) = w` for every `w`. Under each of the following hypotheses, for every `η > 0`
there is `r > 0` such that for `y` in `ball 0 r` and every `X ⊆ ball 0 r`, the set
`{φ (φ⁻¹ y · φ⁻¹ z) | z ∈ X}` has measure at most `(1 + η) λ X`.

- `chart_translation_ultrametric`: `E` is ultrametric and proper, `1 ∈ φ.source` and
  `φ 1 = 0`. The proof gives the stronger bound `λ X`.
- `chart_translation_real`: `E` is also a finite-dimensional real normed space. Its real
  structure is independent of `K`; only norms enter the estimate.

## Main results

Assume `1 ∈ φ.source`, `φ 1 = 0`, and the strict derivative `L` of the group law with
`L (0, w) = w`, as above. Fix `g ∈ H` and a continuous `K`-linear automorphism `A` of `E`. Assume
`z ↦ φ (g · φ⁻¹ z · g⁻¹)` has derivative `A` at `0`. Let `e` be `A` regarded as an additive
homeomorphism (`e x = A x` for all `x`).

- `modularCharacter_le_of_chart_ultrametric`: if `E` is ultrametric and proper, then
  `modularCharacter g ≤ addEquivAddHaarChar e`.
- `modularCharacter_le_of_chart_real`: if `E` is proper and a finite-dimensional real normed
  space, then `modularCharacter g ≤ addEquivAddHaarChar e`.

Here `addEquivAddHaarChar e` is Mathlib's scaling factor of the additive Haar measure under `e`.

## Proofs

The identities about the group law follow from `φ⁻¹ (φ x) = x` on the source and `φ (φ⁻¹ y) = y`
on the target. They use continuity of multiplication and inversion at `1` to keep the points
involved inside the source and target.

`chart_translation_ultrametric` applies `measure_image_le_of_near_translation_ultrametric`
(module `LocalScaling`). Its near-translation hypothesis comes from `near_translation_estimate`
applied to the strict derivative. Its other hypotheses are `chart_mul_zero_eventually`,
`tendsto_chart_inv`, `chart_inv_mul_eventually` and `chart_mul_inv_eventually`. The resulting
bound `λ X` is then weakened to `(1 + η) λ X`. `chart_translation_real` applies
`measure_image_le_of_near_translation` to the output of `near_translation_estimate`.

Both main results apply `modularCharacter_le_of_chart` with `λ` the additive Haar measure
`addHaar` and `D = addEquivAddHaarChar e`. Its hypothesis `hP1` is the left-translation estimate
above. Its hypothesis `hP2` is `measure_image_ball_le_of_hasFDerivAt_ultrametric` or
`measure_image_ball_le_of_hasFDerivAt` (module `LocalScaling`). These apply to the conjugation
map read in the chart, which sends `0` to `0` by `chart_conj_zero`.

## Provenance

This is an internal step, written for this project, toward the Library statement
`Langlands.Global.PlaceGroupPoints.LocalModularCharacterAdjointDeterminantStatement`. It cites no
literature statement. The derivative hypotheses are meant to be supplied by a chart of the group
of points of a smooth affine group over a completion of a number field.

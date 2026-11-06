# Bounding the modular character through a chart at the identity

Module `Langlands.Global.LocalModularCharacter.ChartComparison`.

This module connects the abstract comparison theorem `modularCharacter_le_of_comparison`
(module `ComparisonMeasure`) to estimates in a chart. The group `H` is a locally compact,
Hausdorff, second-countable topological group with its Borel σ-algebra. The model space `E` is a
proper normed additive group with its Borel σ-algebra and an additive Haar measure `λ`
(`l` in Lean). The chart is an open partial homeomorphism `φ : H → E`.

## Definitions

- `chartMeasure l φ R`: the restriction of `λ` to the open ball `ball 0 R` of `E`, pushed
  forward to `H` along `φ.symm`.

## Results

- `chartMeasure_apply`: if `ball 0 R ⊆ φ.target` and `S ⊆ H` is measurable, then
  `chartMeasure l φ R S = λ (φ (φ.source ∩ S) ∩ ball 0 R)`.
- `isFiniteMeasure_chartMeasure` (instance): `chartMeasure l φ R` is finite, because balls in a
  proper space have finite Haar measure.
- `modularCharacter_le_of_chart`: assume `1 ∈ φ.source` and `φ 1 = 0`. Fix `g ∈ H` and a real
  `D ≥ 0`, and assume:
  - `hP1`: for every `η > 0` there is `r > 0` such that for every `y` in `ball 0 r` and every
    `X ⊆ ball 0 r`, the set `{φ (φ⁻¹ y · φ⁻¹ z) | z ∈ X}` has measure at most `(1 + η) λ X`;
  - `hP2`: for every `η > 0` there is `r₀ > 0` such that for every `r ≤ r₀`, the set
    `{φ (g · φ⁻¹ z · g⁻¹) | z ∈ ball 0 r}` has measure at most `(1 + η) D λ (ball 0 r)`.

  Then `modularCharacter g ≤ D`.

  In `hP1` and `hP2`, `φ⁻¹` is Lean's total function `φ.symm`. The hypotheses do not require
  `X` to be measurable; the measure is the outer measure.

## Proof of `modularCharacter_le_of_chart`

Choose `R > 0` with `ball 0 R ⊆ φ.target`, which is possible because `0 = φ 1` lies in the open
target. Apply `modularCharacter_le_of_comparison` to `ν = chartMeasure l φ R` and check its three
hypotheses.

- Positivity. A neighbourhood `U` of `1` contains an open `U' ∋ 1`. The set
  `φ (φ.source ∩ U') ∩ ball 0 R` is open in `E` and contains `0`, so its Haar measure is positive.
  By `chartMeasure_apply` this measure is `ν U' ≤ ν U`.
- Approximate left invariance. Given `η`, take `r` from `hP1` and
  `N = φ.source ∩ φ⁻¹(ball 0 (min r R))`, an open neighbourhood of `1`. For `x ∈ N` and
  measurable `T ⊆ N`, the image `φ (x T)` lies inside the image of `φ T` under
  `z ↦ φ (φ⁻¹ (φ x) · φ⁻¹ z)`. Apply `hP1` with `y = φ x` and `X = φ T`. Since `φ T` lies in
  `ball 0 R`, `chartMeasure_apply` gives `ν T = λ (φ T)`.
- Conjugation. Given `η` and a neighbourhood `U` of `1`, take `r₀` from `hP2`. Choose `r₁ > 0`
  with `ball 0 r₁ ⊆ φ (φ.source ∩ U)`; this is possible because the chart is open at `1`. Put
  `ρ = min (min r₀ R) r₁` and `V = φ.source ∩ φ⁻¹(ball 0 ρ)`. Then `V` is open, contains `1`,
  and is contained in `U` because `φ` is injective on its source. The image `φ (g V g⁻¹)` is
  contained in `{φ (g · φ⁻¹ z · g⁻¹) | z ∈ ball 0 ρ}`, and `λ (ball 0 ρ) ≤ ν V`. So `hP2` with
  `r = ρ` gives `ν (g V g⁻¹) ≤ (1 + η) D ν V`.

## Provenance

This is an internal step, written for this project, toward the Library statement
`Langlands.Global.PlaceGroupPoints.LocalModularCharacterAdjointDeterminantStatement`. It cites no
literature statement. It only translates the chart estimates (proved in `LocalScaling` for the
relevant local fields) into the hypotheses of `modularCharacter_le_of_comparison`.

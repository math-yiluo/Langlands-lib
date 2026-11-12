# Fibre powers of affine charts of separated algebraic spaces are affine

Author: Worker 105.

Helper module for the second countability of rational points
(`EtaleChartSecondCountable`). It is used for Conrad's p.17 claim that adelic points of
separated algebraic spaces have a countable base
(`Langlands.Global.AdelicSpacePointTopologyStatement`).

## Declarations

Namespace `Langlands.AlgebraicGeometry.AlgebraicSpace.ChartFibrePower`. Here `X` is a presheaf on
`Over S` whose diagonal is a representable closed immersion, as for a separated algebraic space.
`a : h_V → X` is a representable map from a scheme `V` over `S`.

- `map_uliftYonedaEquiv`: restriction of the section of a represented map is precomposition.
- `succ_isAffine`: let `S`, `V` and the fibre power `P` be affine. Then the next fibre power
  `succ ha P` (the represented pullback of `a` along `P → X`) is affine.
  - Proof: let `Z ⊆ P ×_S V` be the closed subscheme on which the two maps to `X` agree, given
    by `exists_representsEqualizer_of_relative_diag`.
  - `Z` is affine as a closed subscheme of an affine scheme.
  - The universal properties give mutually inverse maps between `Z` and the new fibre power.
- `fin_isAffine`: all fibre powers `fin ha n` of an affine chart are affine, by induction.
- `exists_of_finite_affine`: for an étale chart from an affine separated scheme and a finite
  nonempty index type, there is a fibre power with three properties: it is separated over `S`,
  it is affine, and its projections are étale. This is the affine refinement of
  `ChartFibrePower.exists_of_finite`.

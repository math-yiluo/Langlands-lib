# Independence of the complex chart on `X(G)` from the lattice basis

Author: Worker 706.

`Langlands.Plancherel.rationalUnramifiedBasisChartIndependence` proves
`RationalUnramifiedBasisChartIndependenceStatement.{u}`. For any two integer
bases `b` and `b'` of the valuation image `Λ(G)` of a connected reductive group
over a nonarchimedean local field, the `b'` coordinate map is a local
biholomorphism when `X(G)` carries the chart of `b`. This is the chart
independence component of the complex torus assertion in David Renard,
*Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, V.3.20, printed p. 116 / PDF p. 122. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`.

## Lean proof

Write `z` for the coordinates of a character in the basis `b`. Its `i`th
coordinate in the basis `b'` is `∏ j, z j ^ (b.repr (b' i) j)`. Lean uses
`rationalImageBasisUnitCoordinates` to reconstruct the image character from
its values in `ℂˣ`, then applies `rationalImageBasisCharacter_apply` and
coerces the resulting product of integer powers to `ℂ`.

Each basis coordinate map is a published open embedding, which gives an open
partial homeomorphism with source all of `X(G)`. On the image of the chart of
`b`, all coordinates are nonzero because they are values in `ℂˣ`. The
transition from `b` to `b'` agrees there with the displayed Laurent monomial
map by the right inverse law of the chart. The coordinate projections are
continuous linear maps. Lean combines their analyticity with analyticity of
integer powers at nonzero values, finite products, and finite tuples.
Exchanging `b` and `b'` proves the same regularity for the reverse transition.

The open partial homeomorphism of the `b'` coordinate map supplies the
partial equivalence for Mathlib's local diffeomorphism predicate. Its forward
map written in the chart of `b` is the transition from `b` to `b'`, and its
inverse written in the chart of `b` is the reverse transition. The extended
charts on the model vector space are the identity. The proof combines the two
analyticity results with continuity of the open partial homeomorphism and its
inverse to obtain `ContMDiffOn` at order `ω` on the respective domains. The
source is all of `X(G)`, so the same witness works at every character.

A second proof constructs the partial diffeomorphism using the coordinate transition in each direction. [Coordinate transition proof](RationalUnramifiedBasisChartTransitionProof.md)

# Exact restriction comparison proposition

Author: Worker 22. The restriction-map definitions are published in
Library commit `ef274d37c255e4b25a990dd377d10e2da436807d`.
`Langlands.Continuous.RestrictionComparisonLaws` is a `Prop`-valued
definition; its proof is a separate contribution.

For every common universe `u`, commutative ring `k : Type u` with a
topology, topological group `G : Type u`, discrete module
`A : DiscreteModule k G`, and open subgroup `H`, it asserts three
commuting squares:

1. At every open normal stage `N`, ordinary cochain restriction followed
   by the subgroup's finite-stage comparison equals the ambient
   finite-stage comparison followed by actual continuous cochain restriction.
2. In every natural degree `q`, the corresponding equality holds on
   actual cohomology at stage `N`.
3. In every natural degree `q`, finite-quotient colimit restriction
   followed by the subgroup's colimit comparison equals the ambient
   comparison followed by actual continuous cohomology restriction.

The continuous maps have their topology forgotten by the existing functor.
The cohomology restriction is exactly the imported `continuousRestriction`,
defined by Mathlib's `ContinuousCohomology.map` for subgroup inclusion.
The proposition assumes no comparison law or equivalence. Compactness and
Hausdorffness are unnecessary for these naturality assertions.

This exact assertion for the named maps is derived from Serre,
*Local Fields* (1979), VII §5, printed pp.115–117 / PDF pp.121–123,
and X §3, printed p.154 / PDF p.160. Its implementation-specific content
is coherence with Mathlib's nested continuous cochain and homology models.
Literature ID `serre-1979-local-fields`; SHA-256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`;
retained file `/home/taskhub/central-library/Serre--Local Fields--1979.pdf`.
Environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.

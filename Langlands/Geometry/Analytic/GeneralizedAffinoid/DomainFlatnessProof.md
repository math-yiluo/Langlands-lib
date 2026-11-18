# Algebraic flatness of full affinoid-domain restrictions

Authors: Worker 5217 and Worker 2037.

This module proves the Library statement
`Langlands.Analytic.PresentedAffinoidAlgebra.Domain.FlatnessStatement`. Let `K`
be a complete ultrametric normed field, `A` a presented affinoid algebra over
`K`, and `U : Domain K A` a full represented affinoid domain. The statement
says that the structural map `U.baseMap : A → U.algebra` is flat as a
homomorphism of the underlying commutative rings. The result is proved for
every such `K`, with no strictness or nontrivial-valuation hypothesis.

## Declaration

`Langlands.Analytic.PresentedAffinoidAlgebra.Domain.flatness :
FlatnessStatement.{u}`.

## Proof

The theorem applies `Domain.flatnessStatement_of_chartFlat` from
`DomainFlatnessReduction` to `RationalChart.flat_baseMap` from
`RationalChartFlatness`. The proof has three layers, each in its own module:

1. `RelativeSeriesFlatness` proves that the structural map of a scalar
   rational presentation with one fraction coordinate is flat
   (`flat_rationalPresentation_baseMap`). The argument is algebraic. Relative
   weighted series are flat over `A` by the equational criterion and a
   bounded lifting lemma. The quotient by `g X - f₀` is flat by a recurrence
   argument on coefficients and Nakayama's lemma.
2. `RationalChartFlatness` extends this to every rational chart
   (`RationalChart.flat_baseMap`). A Laurent chart `{c ≤ |g|}` makes the
   denominator invertible, and then the fraction coordinates are cut out one
   at a time. Charts are compared through their loci.
3. `DomainFlatnessReduction` reduces an arbitrary full domain to rational
   charts (`Domain.flat_baseMap_of_chartFlat`). It uses the Library's finite
   rational cover of a full domain and descent of flatness along the
   faithfully flat product of the chart algebras.

Each module's Markdown explains its proofs in detail.

## Provenance

This proves Berkovich, *Spectral theory and analytic geometry over
non-Archimedean fields* (1990), Proposition 2.2.4(ii), for the Library's full
represented affinoid domains. The route differs from Berkovich's, which goes
through strictly affinoid algebras and ground-field extension. The route here
uses the Library's Gerritzen–Grauert type rational cover and purely algebraic
flatness arguments, as described in the three supporting modules.

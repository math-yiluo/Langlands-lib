# Geometric reduction for supplied relative central quotients

Worker 358.

`RelativeCentralQuotientGeometryReductionStatement` is a `Prop`-valued
definition of the conditional geometry consequence: the kernel is of
multiplicative type, and the supplied target is affine and reductive.
`relativeCentralQuotientGeometryReduction` proves this named assertion
using the parameterized adapters in this module.

This module is a conditional reduction. It proves the geometry clause of
`RelativeCentralQuotientStatement` from two separately named propositions:

- `RelativeMultiplicativeTypeClosedSubgroupStatement`: a flat, locally
  finitely presented closed subgroup of a relative group of multiplicative
  type is of multiplicative type.
- `RelativeCentralMultiplicativeTypeQuotientStatement`: a smooth affine group
  with connected geometric fibres has an affine actual fppf quotient by
  every central closed subgroup of multiplicative type.

These propositions are explicit hypotheses of the theorems here. This
module does not prove either proposition or the full relative central
quotient statement.

`centralKernel_isMultiplicativeType_of_closedSubgroups` applies to a
reductive group `G` over any scheme `S`, a central closed subgroup
`z : Z ⟶ G`, and an actual fppf quotient whose full kernel range is the
range of `z`. The published `reductiveRelativeCenter` supplies a closed
centre representative of multiplicative type. Centrality factors `z`
through this representative, and the factor is again a closed immersion.
`FppfQuotientKernelGeometry` supplies flatness and local finite presentation
of `Z` over the base from the actual kernel square. The first input
proposition therefore proves that `Z` is of relative multiplicative type.
No separate flatness assumption is needed.

`RelativeRoot.IsFppfQuotient.isAffineHom_target_of_centralMultiplicativeTypeQuotients`
uses the second input proposition to construct an affine quotient with
the same full kernel as the supplied quotient. The general fppf comparison
isomorphism transfers affinity to the supplied target. This theorem takes
multiplicative type of `Z` as an explicit hypothesis.

`isReductive_target_of_multiplicativeType_geometry` combines these two
steps and applies `isReductive_target_of_central`, which descends
smoothness and verifies reductivity on geometric fibres.

The module is an internal derived adapter between the named Library
interfaces, kernel pullback geometry, and quotient uniqueness. The
underlying source target is the geometry assertion of the existing
`RelativeCentralQuotientStatement`; no additional source translation is
introduced.

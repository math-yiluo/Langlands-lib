# Bounded universal property of the strict Tate algebra

Author: Worker 36.

`Langlands.Analytic.StrictTateAlgebra.boundedUniversalProperty` proves the
exact four-part `BoundedUniversalPropertyStatement`. The existing
`boundedHomEquiv` also packages its coordinate correspondence as an actual
equivalence. Coordinate and continuous-map definitions are in
TateUniversal.Definitions; raw evaluation formulas are in TateEvaluation.Definitions.

The coordinate elements are the genuine degree-one restricted monomials.
Their norms are one. The finite monomial identity is inherited from the
corresponding identity of formal power series, through the actual subalgebra
inclusion. An algebra map therefore sends each monomial to its scalar
coefficient times the finite product of its coordinate images.

A bounded algebra homomorphism gives a continuous linear map, using its
existing norm bound. Apply it to the norm-convergent monomial expansion from
TateSeries. This proves that the homomorphism evaluates each series as the sum
of its evaluated coefficient monomials. Hence coordinate images determine the
entire bounded algebra map. Since source monomials with coefficient one have
norm one, a single bound for the map bounds every monomial in its coordinate
images.

Conversely, TateEvaluation constructs evaluation for every tuple whose
monomials share a positive norm bound. It sends each coordinate to the supplied
element. These two constructions are inverse, giving an actual equivalence
between bounded algebra maps and bounded-monomial tuples. Neither a
normalized target unit norm nor a nonzero target is needed. The source field
is complete for its norm-convergent expansion; the target algebra is complete
and ultrametric for the inverse evaluation construction. The index set may
be arbitrary; finite index sets give the strict affinoid use case.

This is internal foundational work for the strict Tate algebra convention
in Berkovich's Trieste 2009 lectures, Example 1.2.2(v) and Definition 2.1.2.
The construction uses TateAlgebra, TateSeries, Affinoid and TateEvaluation.
The closing theorem assembles the finite power-bound comparison, convergent
evaluation and its constructed bounded homomorphism, coordinate uniqueness,
and unique coordinate-prescribing extension. The last uniqueness proof applies
`hom_ext` to the constructed evaluation map. No analytic-domain representability
is asserted.

Registered original: `berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Exercise 2.1.5(i), pp.7-8, supplies the original extension context. The exact
derived scope and explicit bounded-monomial hypothesis are explained in
TateUniversal/Statement.md.

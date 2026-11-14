# Weights of stable coordinate lines over local rings

This internal algebraic module gives a criterion for a split torus to act through
one character on a chosen coordinate. The base is any commutative local ring,
including rings with nilpotents.

`exists_isHomogeneous_of_stable_line` assumes that scalar multiplication by the
chosen element is injective and that every torus weight projection of it lies
in its scalar span. The projections sum to the element, so their scalar
coefficients sum to one. Over a local ring one coefficient is a unit. That
projection is homogeneous, and multiplication by the inverse unit makes the
original element homogeneous of the same weight.

`homog_eq_span_of_aeval_surjective` says that the degree of a positive homogeneous
polynomial generator is its scalar span. The proof writes an element as a
polynomial and applies the degree projection, which isolates the coefficient of
degree one. `smul_injective_of_aeval_injective` obtains injectivity of scalar
multiplication by comparing coefficients of the polynomials `r X` and `s X`.

`exists_isHomogeneous_of_preserves_degree` combines these facts: a positive
homogeneous polynomial coordinate is a torus eigenfunction if every torus
projection preserves its degree. Degree preservation is an explicit premise.
`coordinateWeightOfPreservesDegree` chooses such a weight, and
`isHomogeneous_coordinateWeightOfPreservesDegree` proves that the coordinate
is homogeneous of this chosen weight.
The module does not yet verify that premise for a dynamic root group, identify
the resulting character with its root, or assert the isomorphism theorem.

The provenance is the internal combination of `TorusGrading`'s homogeneous
projections with `GradedLineFlatLocal.comp_aeval` and the elementary local-ring
unit criterion for a finite sum. No external source is used.

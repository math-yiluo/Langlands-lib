# Vector-bundle series for arbitrary split contracting groups

This derived unit assumes a reductive group over the spectrum of an arbitrary
commutative ring, a fibrewise maximal coordinate split torus, a finite fibrewise
root datum and actual additive-group parametrizations for all its roots.
The coordinate cocharacter is arbitrary: zero root weights are allowed.

For a supplied `SplitParabolicWeightChart`, its exact natural weight values
prove nonnegative pairings on every root in its positive base. Root negation
then proves nonpositive pairings on the complementary roots. The actual
root parametrizations provide the equivariant open split cell for precisely
these root lists.

`isRepresentedBy_weightInclusion` applies the all-test supported-coordinate
comparison to that cell. The chart's positive-weight term, followed by the
ambient inclusion of its regular contracting group, represents exactly the
dynamic contracting functor of the originally supplied cocharacter.
`dynamicIso` identifies that positive-weight term with the actual affine
contracting group of the original cocharacter. `dynamicIso_hom_comp`
records equality of the specified ambient maps.

`hasFiniteVectorBundleSeries` transports the root-weight series along this
isomorphism. `hasFiniteVectorBundleSeries_splitContractingGroup` obtains the
adapted chart from reductivity and the supplied actual root parametrizations.
The proof works at arbitrary universe, with empty root sets and arbitrary
commutative base rings; it imposes no noetherian or connectedness assumption.

Provenance is the existing adapted-chart construction, actual split big cell,
all-test positive-weight comparison and root-weight-series transport.
This unit supplies the split contracting-group case. It does not identify
arbitrary supplied relative radicals or prove compatibility and descent of
the resulting filtration between different split charts.

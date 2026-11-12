# Connected fibres of a target family after arbitrary scheme base change

This internally derived supporting unit identifies geometrically connected
nonempty fibres of the changed morphism with structural geometrically connected
nonempty fibres of the changed target-chart family. The original target chart
is assumed surjective and etale. The comparison imposes no affine, finiteness,
separation or representability assumption on the spaces or morphism.

`baseChangeTestFibreHomeomorph` is defined for every represented scheme test of
the restricted chart. It compares the actual structural fibre of the family
base changed along the projection from V times T to V with the actual fibre
of the changed morphism at that chart test. It composes the structural
base-change homeomorphism, the original target-family test homeomorphism, the
chart-restriction identity under the slice adjunction, and the inverse of the
fibre restriction homeomorphism. The adjoint original test has precisely the
required projection to V; no identification of different structural maps is
assumed.

`hasGeometricallyConnectedFibres_baseChange_iff` proves the stated equivalence.
Forwards, a structural field test of the changed family is unique over the
represented terminal base and is therefore the represented chart test.
The homeomorphism transfers the given connectedness of the changed morphism's
fibre. Conversely it suffices to test algebraically closed fields. The
restricted chart remains etale and surjective, so every such target point
lifts to it. Connectedness of the corresponding structural fibre transfers
back through the same homeomorphism, followed by the pullback isomorphism for
the lift equation. All connected-space assertions retain nonemptiness.

The provenance is composition of existing Library fibre comparisons, slice
adjunction, preservation of chart properties, and the already proved
algebraically closed field criterion. This unit proves the arbitrary-base
comparison needed for the limit argument; eventual connected-fibre descent
and the full eight-property host theorem remain separate obligations.

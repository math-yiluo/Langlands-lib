# Connected nonempty geometric fibres descend along affine limits

This internally derived supporting unit proves the connected-fibre clause of
`SpaceLimitPropertyDescentStatement`: the exact predicate
`SpaceLimitPropertyDescends (fun f => HasGeometricallyConnectedFibres f)`.
It retains arbitrary cofiltered index categories in the declared universe,
affine stage schemes, quasi-separated source and target algebraic spaces,
and their quasi-compact locally finitely presented etale surjective atlases.
It adds no hypothesis. The connected-fibre predicate includes nonemptiness.

`AffineTargetFamily.connectedFibreLocusOver f b g` is the inverse image of the
canonical geometric-component count-one locus of the actual target-chart
family under the projection from the changed chart to the original chart.
The corresponding constructibility theorem follows from the already proved
affine constructibility of the component-count locus and inverse-image
preservation of constructibility for scheme morphisms. The family retains
relative quasi-separatedness and its finite-presentation atlas by the existing
actual-family theorems, under precisely the listed hypotheses.

`AffineTargetFamily.hasGeometricallyConnectedFibres_iff_locus_eq_univ` identifies
the changed morphism's connected nonempty geometric fibres with this locus
being the whole changed chart. It applies the actual arbitrary-base-change
family criterion, the structural component-count base-change criterion, and
the symmetry of the actual scheme pullback to use the varying-factor-first
orientation of the limit diagram.

`spaceLimitGeometricallyConnectedFibresDescent` chooses an affine
finite-presentation atlas of the stage target. It restricts the index diagram
to the incoming slice category over the specified stage, using the already
proved initial-functor limit comparison. The actual target-base-change
diagram of this restriction is a diagram of affine schemes. Its limit is the
actual changed target chart, supplied by the existing limiting cone for a
given pullback square. The cone projections and diagram transitions commute
with projection to the fixed original chart.

If the limit morphism has the fibre property, the good locus is the whole
limit chart. Its constructible inverse image at the identity object of the
incoming slice therefore has full inverse image on the limit. The existing
constructible affine-limit detection theorem produces one incoming stage
where its inverse image is the whole stage chart. Naturality identifies that
inverse image with the good locus on that stage. The good-locus criterion
then gives the desired fibre property for the stage morphism. Conversely,
preservation of connected nonempty geometric fibres under scheme base change,
followed by the natural isomorphism comparing iterated and direct base change,
transports any incoming-stage property to the limit.

The proof route is an internal composition of the actual target-family fibre
comparisons, geometric-component constructibility, scheme pullback limit
construction, constructible-set detection, and isomorphism transport already
in the Library. The theorem proves the eighth clause; the other seven clauses
and the assembled full theorem are not asserted by this unit.

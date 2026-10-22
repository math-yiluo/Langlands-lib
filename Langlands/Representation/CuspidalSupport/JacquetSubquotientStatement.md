# Actual subquotients under normalized Jacquet descent

Author: Worker 72. This pair states two internal interfaces needed to descend a
common actual subquotient in the cuspidal-induction association argument. It
contains proposition definitions only.

`NormalizedJacquetSubquotientTheorem` says that the canonical normalized Jacquet
functor sends an actual smooth subquotient to an actual smooth subquotient.
Both objects in this clause have the same carrier universe, as required by the
published categorical `SmoothRep.IsSubquotient` predicate. The conclusion uses
that same predicate and the published Jacquet functor; it does not replace the
quotient or its action by abstract data.

`NormalizedJacquetEquivalenceTheorem` says that an actual intertwining linear
equivalence between smooth ambient representations induces an actual
intertwining linear equivalence between their normalized Jacquet modules.
The two carrier universes are independent. This permits two actual subquotient
presentations of a common representation to be descended separately and then
compared without resizing a carrier or identifying two smooth categories.

`JacquetSubquotientTransportTheorem` combines the clauses. Both quantify every
prime, every actual p-adic field and compatible topological realization, every
natural rank including zero, and every standard block shape. Neither clause
requires irreducibility, cuspidality, finite length, or finite dimension.

## Internal provenance

These are algebraic consequences of the published normalized Jacquet
construction and its exactness. A subquotient admits a presentation by a smooth
representation embedding in the ambient object and surjecting onto the
subquotient. Exactness preserves the injection, and the actual quotient maps
preserve the surjection. The same presentation then supplies the conclusion.
The equivalence clause follows by applying the actual normalized Jacquet map
to an intertwining equivalence and its inverse, using the proved identity and
composition laws. These are intended proof routes, not assumptions of either
proposition.

The relevant existing proof interfaces are
`SmoothRep.isSubquotient_iff_exists` in
`Classification.SupercuspidalSupport`, and the actual map/exactness results in
`Parabolic.NormalizedJacquetExactnessProof`. The statement imports only the
underlying definitions. It does not assert the main association theorem or any
minimal-Jacquet or filtration theorem.

# Proof of the tempered results from building data

`Langlands.Aubert.General.RepresentedParabolic.temperedDiscreteSeriesFromBuilding`
proves `TemperedDiscreteSeriesFromBuildingStatement.{u, v}` at independent local-field
and representation-carrier universes. Its premise is existence of data satisfying
the one-group building axioms. [Statement](TemperedDiscreteSeriesFromBuildingStatement.md)

`bruhatTitsAvailabilityReduction` chooses the one-group data and supplies the
comparisons between groups and compatibility with isomorphisms. From this
availability, `casselmanFromBuilding` gives the corrected Casselman
biconditional. Its sufficiency uses a Cartan decomposition and a
simultaneous compact-open Iwahori basis at a common special vertex.
[Casselman's criterion from availability](CasselmanFromBuildingProof.md)

For VII.2.4, temperedness gives admissibility, and `unitaryCentralCharacter`
provides the unitary central character required by Casselman's criterion. It
uses the given character on a nonzero representation and the trivial character
on the zero representation. The criterion for the supplied quotient Haar measure
identifies square integrability modulo the center with the strict root-cone
condition on the normalized real parts of the represented Jacquet exponents.
The proof composes this biconditional with
`hasPositiveRepresentedJacquetExponents_iff_unitaryJacquetParts_vanish`,
which identifies that positivity with vanishing of the unitary Jacquet part at
each proper represented rational parabolic.
[Positivity and vanishing](TemperedPositiveJacquetExponents.md)

For the VII.2.6 embedding equivalence, the proof supplies this criterion
and the theorems on square-integrable representations being tempered,
normalized induction preserving temperedness, and parabolic quotient
compactness to `temperedIrreducibleDiscreteSeries_of_inputs`. The reduction takes
an irreducible quotient of the unitary Jacquet part at a minimal parabolic with
nonzero unitary part. It uses the criterion on the Levi to obtain square
integrability for every Haar measure in the statement, and Frobenius reciprocity
to obtain the embedding. In the reverse direction, temperedness passes from
the square-integrable inducing representation to the normalized induction
and then to the embedded representation.

For the corollary, `temperedIrreducibleUnitarizable_of_discreteSeries` takes
the embedding equivalence together with reductive unimodularity, existence
of standard cocharacters, and parabolic quotient compactness. This reduction
induces a positive-definite invariant Hermitian form from the square-integrable
Levi representation and restricts it along the embedding.
[Discrete-series and unitarizability reductions](TemperedIrreducibleDiscreteSeriesReduction.md)

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French edition
dated 9 July 2026. VII.2.4 Lemma, printed p. 230 (PDF p. 236), and VII.2.6
Theorem, embedding equivalence, and Corollary, printed pp. 231–232
(PDF pp. 237–238). The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

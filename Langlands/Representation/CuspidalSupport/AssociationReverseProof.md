# Common cuspidal-induction subquotients force association

Authors: Workers 72 and 120. Worker 72 implemented the Jacquet descent and
filtration argument; Worker 120 supplied the canonical-object interface used
by the closing theorem.

`Langlands.CuspidalSupport.cuspidalInductionReverseAssociation` proves the
published `CuspidalInductionReverseAssociationTheorem`. For every prime,
actual p-adic field, compatible topological data and natural rank, two
irreducible cuspidal inducing representations are associated if their
canonical normalized inductions have a common actual irreducible
subquotient. The field and the two inducing-carrier universes remain
independent. The theorem includes rank zero and adds no hypotheses.

The supporting lemmas are in the namespace
`Langlands.CuspidalSupport.AssociationReverse`. Their induction objects use
the published normalized parabolic induction functor. These objects are
definitionally the canonical smooth inductions in the statement, so the
closing theorem applies the supporting implication directly.

`commonJacquetDescent` starts with equivalent nonzero actual subquotients
of the two inductions. The published `minimalNonzeroJacquet` theorem
chooses a Levi on which the first object's Jacquet module is nonzero and
Levi-quasicuspidal. The published normalized Jacquet subquotient and
equivalence transport theorems retain both actual subquotient
presentations and their representation equivalence. Quasicuspidality
transfers through that equivalence. If either source Levi were
nonassociated to the chosen Levi, the published
`nonassociatedJacquetSubquotients` theorem would make the corresponding
quasicuspidal Jacquet subquotient subsingleton. Its equivalence with the
first nonzero Jacquet module gives a contradiction. Thus both source
Levis associate to the chosen Levi.

`associatedJacquet_simpleFactors` checks that the grades of an associated
Jacquet filtration are irreducible when the inducing representation is
irreducible. Each supplied grade equivalence identifies the grade with
the inducing representation pulled back along a Levi group equivalence.
Irreducibility under surjective pullback and representation equivalence
therefore gives simple factors.

`commonSubquotientAssociated` unpacks the actual subrepresentation and
quotient witnesses of a common irreducible subquotient. Its first
quotient is nonzero. Applying the descent lemma gives equivalent nonzero
Jacquet objects and both Levi associations. The published
`associatedJacquetFiltration` theorem supplies a finite filtration of
each Jacquet induction, with grades equivalent to the permutation
transports of its inducing representation. The preceding lemma makes
both filtrations have simple factors.

The target Jacquet induction is Artinian by the published finite-length
criterion, and the actual subquotient inherits Artinianness by
`smoothSubquotientArtinian`. The Jacquet equivalence is a nonzero
intertwiner because its source is nonzero and its underlying map is
injective. Applying `nonzeroHomCommonSubquotient` to that map produces
equivalent actual irreducible subquotients of the two Jacquet objects.
This step does not assert that either Jacquet object is irreducible.

The published `smoothSubquotientTransitivity` theorem makes these simple
objects actual subquotients of the two Jacquet inductions. Unpacking the
resulting presentations and converting their isomorphisms with
`SmoothRep.equivOfIso` lets `simpleSubquotientFactor` match each with a
grade of its supplied filtration. The extraction is applied separately
at carrier universes `max uF uV` and `max uF uW`; the equivalence between
the simple objects retains the independent universes.

Composing the grade equivalences with the equivalence of simple objects
associates both original inducing representations to a single actual
representation of the descent Levi. The published symmetry and
transitivity laws for `RepresentationsAssociated` finish the argument.
They preserve the actual coordinate permutation and inverse-conjugation
transport required by the statement.

This is a proof of the reverse direction extracted from the third
equivalence of `CuspidalInductionAssociationTheorem`. The argument uses
the published Jacquet results at every rank and has no positivity,
finite-dimensionality or additional theorem premise. The forward
intertwiner and Jordan–Hölder factor implications of the full association
theorem remain separate obligations. The motivating source and the
scope of this internal extraction are recorded in the unchanged
statement pair; this proof explains its implemented route.

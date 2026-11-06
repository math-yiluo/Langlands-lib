# Actual Jacquet families witnessing a composition-length bound

This module defines an internal geometric/support witness and states its existence
for maximal-Levi supercuspidal induction. The existence statement is unproved.
The companion reduction proves that such a witness implies the represented
length bound and, for reducible induction, the actual two-endpoint statement.

## The internal witness

`HasRepresentedJacquetLengthWitness A bound` concerns an actual smooth complex
representation `A` of the rational points of an affine group scheme over a
Hausdorff topological field. The ambient point group has its canonical topology
and is locally compact and nonarchimedean. Field universe `u` and representation
carrier universe `w` are independent.

The predicate asserts existence of a finite family, indexed by `Fin n`, of
represented rational parabolics in the same ambient group. Every member supplies
its actual parabolic map, rational Levi, geometric unipotent radical and matching
multiplication isomorphism. Each radical's literal point image is a limit of
compact subgroups, in the imported sense that every compact subset is contained
in a compact subgroup. Each Jacquet functor takes values in the rational points
of its own Levi, with that Levi's canonical topology.

There are natural numbers `b i` with sum at most `bound` such that the actual
composition length of the `i`th Jacquet image of `A` is at most `b i`.
Composition length is `repLength`, with values in `ℕ∞`; infinite length is
excluded by this bound. Finally, every actual irreducible smooth subquotient `D`
of `A`, in the same carrier universe, has a nontrivial image under at least one
of these functors. This quantifies over every such subquotient, without a chosen
composition series or a finite-length premise.

The family is not required to be indexed by standard Levis, and its members
need not be distinct or proper. This deliberately internal formulation records
the inputs needed by the published `exactFamilyLengthBound`; it does not
construct the source's standard family or assert a Weyl-group identification.

## The maximal-Levi target

`MaximalLeviSupercuspidalJacquetLengthWitnessStatement.{u,v}` retains the field,
topology, connected reductive group, actual maximal proper parabolic, rational
Levi and radical scope of
`MaximalLeviSupercuspidalInductionLengthBoundStatement.{u,v}`. Its inducing
representation is irreducible and supercuspidal, where supercuspidality is
vanishing of every normalized Jacquet module along every proper represented
parabolic of the Levi. The conclusion is a witness of budget two for the actual
normalized induction. Its carrier universe is `max u v`; there is no
central-character or finite-length premise.

This is a derived proof interface, rather than a quotation of Renard or a proof
of the length bound. In Renard 2026, VI.5.4, printed pp.173–174 / PDF
pp.179–180, the proof sums Jacquet lengths over standard Levis conjugate to the
inducing Levi. VI.5.3 supplies the image-length bounds, and VI.2.1 together with
VI.5.3 supplies detection of every irreducible subquotient. V.4.8, printed
p.122 / PDF p.128, gives total budget two for a maximal proper Levi. Conjugation
reduces the arbitrary parabolic to that standard situation. The present
predicate keeps the actual represented functors and makes the compact-limit
input for exactness explicit. Existence of the family, its compact-limit
radicals, its total image bound and its detection property remain proof
obligations.

The governing source is the registered 9 July 2026 edition
`renard-2026-representations-groupes-reductifs-padiques`. The 2010 corrections
and complements, PDF p.13, correct the earlier VI.5.4 bound to a non-strict
inequality and the adjunction indices to `P′, M′`; the governing edition already
contains these corrections. Neither the new predicate nor its existence
statement supplies the final unitarizable-constituent theorem.

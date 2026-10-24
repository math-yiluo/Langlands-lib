# Positive-rank irreducible cuspidal operator realizations

This internal construction uses the published actual `OperatorRealization`
and its full-operator equivalences. The coefficient field is complex, the
number field `F : Type u` has arbitrary universe, and compactness of
`AdeleQuotient F` is retained explicitly for normalized constant terms.
The index `r : ℕ` denotes actual general linear rank `r + 1`, so every object
has positive rank.

`CuspidalOperatorRealization F r` retains an actual invariant subspace of the
stable automorphic function space, irreducibility of its entire concrete
operator action, and cuspidality of its actual form image. The full action
includes finite adelic translations, standard infinite compact translations
and the genuine enveloping differential action. Its existing faithful maps
to forms and continuous adelic functions are accessed through `realization`.
No arbitrary representation carrier replaces this embedded subspace.

Irreducibility supplies a simple module over the monoid algebra of the full
operator monoid. Its nontriviality transfers through the existing
`asModuleEquiv` to the realized carrier. The finite image is consequently
nonzero: a nonzero source vector cannot map to zero under the injective
form inclusion. This proves the nonzero condition required by subsequent
finite tensor presentations without asserting irreducibility of the finite
restriction.

The vectorwise cusp theorem and proper two-block constant-term equations
specialize the published realization results. Each constant term uses the
existing normalized Haar measure; the positive split hypotheses and equality
of the split rank to `r + 1` remain explicit. `HasCentralCharacter` is an
optional condition on the actual embedded forms using the existing
continuous idele-class character convention; no character is chosen.

The equivalence relation uses complex linear equivalences intertwining the
whole concrete operator algebra. Its reflexivity, symmetry and transitivity
are inherited from representation equivalences. `IsoClass` is the quotient
of these actual irreducible cuspidal objects, and equality of classes is
proved equivalent to nonempty full-operator equivalence.

`IsoClass.toOperatorClass` forgets the cusp and irreducibility witnesses.
It is well-defined and injective because both quotients use exactly the same
full equivalence relation on the selected objects. Composing it with the
published finite-class map gives `finiteClass`; this latter map is not
asserted injective. Every class has an actual cuspidal representative by
quotient surjectivity. These constructions do not assert that cuspidality or
a prescribed central character of one embedding transfers to every
isomorphic embedding.

`PositiveRankCuspidalClass F` is the dependent sum of these fixed-rank
classes over all natural indices. Its rank is the index plus one, with a
proved positivity theorem. Insertion of a fixed-rank class is injective;
for actual objects at one rank, equality after insertion is exactly full
operator equivalence. Distinct ranks give distinct mixed-rank classes.
This provides a class carrier for mixed-rank families, not an isobaric sum
construction.

The provenance is internal: restriction to objects satisfying published
properties, simple-module nontriviality, injective images, and quotient and
dependent-sum constructions. No new identification with original literature
is asserted. The module proves no occurrence of such objects, exhaustion of
the stable core by all forms, full automorphic subquotient category, tensor
factorization, unramified spectral existence, or descent of spectra across
different tensor presentations. Those construction and theorem obligations
remain separate.

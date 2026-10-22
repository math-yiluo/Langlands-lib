# The residue comparison for adic completion integers

For any number field `K : Type u` and finite place `p`, this module identifies
`LocalGalois.baseIntegers (FiniteCompletion K p)` with
`p.adicCompletionIntegers K` by the identity function on the same completed field.
Mathlib's `Valued.toNormedField.norm_le_one_iff` proves that their defining
membership predicates agree. The ring equivalence `normIntegersEquivAdic`
therefore changes only the proof of integrality, and its coercion to the field
is the identity. It sends the published `CompletionResidue.integersMap` to
Mathlib's canonical algebra map from the global ring of integers.

The definition `adicResidueEquiv` composes the already published
`CompletionResidue.residueEquiv` with the residue-field equivalence induced by
this ring equivalence. Thus it compares `RingOfIntegers K / p` with the residue
field of the actual adic integer ring without repeating the approximation or
surjectivity proof of `CompletionResidue`. The lemma `adicResidueEquiv_mk`
identifies its value on every global integer with canonical embedding followed
by reduction in the adic integer ring. This follows from the original
`residueEquiv_mk` and functoriality of the residue map.

The existing finiteness of the global quotient transfers across the equivalence.
Consequently the adic residue field has cardinality `Ideal.absNorm p.asIdeal`.
All declarations retain the arbitrary universe `u` of the number field.

This is internal derived infrastructure: it transports the existing published
comparison along equality of the norm and valuation unit balls, using pinned
Mathlib's residue-field functor. No external literature theorem is transcribed.
The module supplies a one-field comparison only. It does not assert compatibility
between two extension scalar structures, equality of inertia degrees, or the
completed local degree lower bound; those remain separate obligations.

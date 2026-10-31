# Decreasing-induction heads of supplied segment socles

This internal supporting module transfers strong constituent relations to actual
representations supplied by a caller. It does not prove individual-segment
constituent existence or the juxtaposed case of Zelevinsky Proposition 4.6.

The algebraic lemmas preserve the common, arbitrary carrier universe and the
group universe. `IsIrreducibleHead.of_targetEquiv` transports a strong head through
an actual equivalence of its target. The irreducibility proof is transported by
the published equivalence-invariance lemma; composition with an injective
equivalence leaves the quotient map's kernel unchanged.
`IsIrreducibleHead.nonempty_equiv_of_quotient` identifies any irreducible
quotient with the supplied strong head. The proof identifies both targets with
the canonical head, using equality of their quotient kernels.
`IsIrreducibleHead.nonempty_equiv_of_quotient_of_surjective` applies that result
after composing two surjective intertwiners.

For an actual p-adic field and compatible topological realization,
`IsSegmentSocle.nonempty_equiv` compares two supplied strong socles of one
segment. It first expresses both inside the increasing induction of the same
supercuspidal representative using `isSegmentSocle_iff`, then identifies their
images with the canonical socle.
`IsSegmentSocle.isIrreducibleHead_down` assumes the published proposition
`SegmentZelevinskyConstituentExistence` explicitly. Its witness is a strong
segment socle and a strong head of every corresponding decreasing induction.
Socle equivalence and target transport make the caller's supplied segment socle
that same strong head. The field and original supercuspidal carrier universes
remain independent.

`IsSegmentSocle.decreasingHeadQuotient` chooses an actual intertwiner from this
decreasing induction onto the supplied socle and retains its surjectivity in a
subtype. This is the map needed for lifting through normalized product induction;
its construction assumes the same individual-segment existence proposition.

The provenance is an internal deduction from the existing definitions of strong
heads and socles, canonical constituent equivalences, representative invariance
of segment induction, and irreducibility under equivalence. The existential
segment assertion is a hypothesis, not an imported proof. No multisegment
classification, irreducibility criterion, commutation, linked gluing, derivative
or Jacquet result is used. This module supplies a preliminary step of part H of
task `0c90f7e4-78fa-43fd-8736-238bb3e8617d`; it does not construct the quotient
map from a union's full decreasing induction to a product of segment socles.

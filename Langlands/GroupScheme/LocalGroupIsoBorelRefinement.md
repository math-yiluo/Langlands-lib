# Borel-preserving refinements of natural local group isomorphisms

For reductive group schemes G and H over an arbitrary scheme S, chosen relative
Borel subgroups i : B to G and j : C to H, and a natural local group isomorphism
e parameterized by U over S, `LocalGroupIso.borelPreservingRefinement`
constructs the following data:

- a parameter scheme V over S and a map r : V to U whose underlying scheme
  morphism is etale and surjective;
- a source group point h : V to G;
- preservation of the two represented subgroup functors by the refined family
  twisted by conjugation with h, on every relative test scheme.

No affineness or covering hypothesis on U to S is required for this
construction. If U to S is itself etale and surjective, the new parameter
scheme has the same properties by composition.

The record `BorelPreservingRefinement` retains the actual parameter, map,
etaleness, surjectivity, cochain and preservation proof. Its data fields can
also be used with arbitrary supplied subgroup inclusions, although the
constructor proves existence for relative Borel subgroups of reductive groups.

The proof first recovers the actual isomorphism between G and H over U.
Arbitrary base change and transport along this isomorphism give two relative
Borel subgroups of H over U. The published relative Borel conjugacy
construction, applied to the proved relative parabolic conjugacy theorem,
gives an etale cover of U and conjugating sections. The equivalence between
base-changed range equality and all-test conjugacy identifies these sections
as range conjugators. They assemble into a section over the disjoint union of
the cover schemes. Etale locality of range conjugators proves its conjugacy
property on the entire disjoint union. Collapsing the cover gives a single
etale surjective morphism. The inverse image under e of the projected
conjugating section is the required source cochain.

The cover-point equivalence identifies membership in any actual subgroup
range before and after base change. A conjugator of the image of a source
subgroup under the recovered actual isomorphism with a target subgroup then
gives a subgroup-preserving local family: project the conjugating section,
take its inverse image under the local isomorphism, and twist by source
conjugation. The proof checks this on every relative test using range
membership and cancellation of conjugation.

A cocycle and a local family have compatible twists: the new discrepancy is
f(b) inverse times the old discrepancy times f(c). The same formula preserves
all-refinement innerness without assuming that the acting group is faithful.
`BorelPreservingRefinement.hasInnerDiscrepancy` applies this to the image of
the source cochain under any group homomorphism q. If an action restricts to
source conjugation along q, `twist_conjugation_eq` identifies the two twists,
and `BorelPreservingRefinement.preservesSubgroup` gives Borel preservation for
the quotient-action twist.

The provenance is internal. The module derives its constructions from the
published base-change/local-isomorphism equivalence, relative Borel transport
and conjugacy, represented subgroup ranges, etale locality of all-test range
conjugators and Mathlib's coproduct cover. The private helpers assemble
conjugators on a disjoint union and specialize that construction to relative
Borels. The proof uses these published results directly; there is no new
literature assertion. Borel-stabilizer representability and cocycle vanishing
remain separate obligations, as do quasi-split existence and uniqueness.

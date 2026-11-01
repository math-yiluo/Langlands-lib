# Realizations and their actual zero-denominator quotients

This internal derived construction connects existing actual
`OperatorRealization` spaces with their existing actual module quotients by
zero. It retains an arbitrary number-field universe, every natural matrix
rank and complex coefficients. There is no CM-field or character hypothesis.

Write `pS` for `S.toSubquotientEquiv`, the published whole-operator
equivalence obtained from the actual canonical quotient projection.
`toSubquotientEquiv_apply` identifies this equivalence with the projection
on every vector.

`Intertwiner.toSubquotient` sends every whole-operator realization map `L`
to `pT ∘ L ∘ pS⁻¹`. `Intertwiner.ofSubquotient` sends every map between
the two zero-denominator quotients to `pT⁻¹ ∘ L ∘ pS`.
Both maps are constructed by composition of actual representation
intertwiners. Their formulas hold on all vectors. The forward map commutes
with the canonical projections; the corresponding equality of composites is
`toSubquotient_naturality`.

Cancellation of the actual representation equivalences proves both inverse
identities. `Intertwiner.toSubquotientLinearEquiv` bundles them as a
complex-linear equivalence of the entire intertwiner spaces. Its linearity
uses the target equivalence's addition and scalar laws with the pointwise
module structure on intertwiners. Identity and composition are preserved.
Bijectivity and equality reflection follow from the same linear equivalence.
This is a fully faithful map construction; no category instance is added.

`Equivalence.toSubquotient` transports genuine whole-action equivalences
using the same conjugation. Its underlying intertwiner is exactly the
constructed map transport. Conversely, an equivalence between the actual
zero-denominator quotients composes with `pS` and `pT⁻¹` to recover a
whole-action equivalence between the original realizations.
`toSubquotient_equivalence_iff` records preservation and reflection.

`toSubquotientSubrepresentationOrderIso` applies the published
image/preimage construction with the identity operator parameter map and
`pS`. It identifies all whole-action invariant subspaces.
`toSubquotient_isIrreducible_iff` follows from preservation of simple
orders; the irreducibility condition includes nontriviality.
`toSubquotientFiniteEquiv` restricts the canonical whole-action equivalence
along the actual finite-operator homomorphism.

`IsoClass.toSubquotient` descends the zero-denominator construction to
whole-action classes of actual realized spaces. Its injectivity follows by
quotient induction in both arguments and the equivalence reflection above.
`IsoClass.toSubquotientEmbedding` bundles this injection. Its exact equality
criterion retains all concrete operators, rather than merely the finite
restriction. `finiteClass_toSubquotient` proves that this embedding commutes
with the existing finite smooth class maps: the inverse canonical finite
equivalence followed by the existing actual finite-image equivalence
identifies the two finite representations.

Provenance is internal. These are elementary composition, cancellation,
linearity and quotient-descent constructions on the published actual
zero-denominator quotient and its canonical representation equivalence,
Mathlib's genuine intertwining maps and the published invariant-subspace
image/preimage construction. No new identification with original literature
is claimed.

The construction does not identify quotient presentations, assert that
every operator quotient is equivalent to an embedded realization, or
construct a nonzero or irreducible spectral constituent. It adds no
quotient topology, function evaluation or local-factor selection.

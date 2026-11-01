# Actual adjacent factor comparison

Let \(A,B\) be supplied supercuspidal objects of the same positive rank,
with \([A]=\nu[B]\). Write \(P=A\times B\) and \(R=B\times A\), on the
literal standard two-block shape. For any actual nonzero proper invariant
subspaces \(S\subset P\) and \(U\subset R\),
`decreasingSubrepresentation_equiv_increasingQuotient` proves an actual
equivariant linear equivalence
\[
 S \simeq R/U.
\]
The smooth subrepresentation and quotient are the actual submodule and
module quotient objects. The supplied field and topological data are
retained; the supercuspidal carriers lie in `max uF uV`.

The presence of \(S\) proves \(P\) is reducible. If \(R\) were irreducible,
the existing irreducible equal-rank product swap would identify \(R\)
with \(P\), contradicting this. This proves `twoBlock_reducible_swap`
for any two irreducible smooth equal-rank factors. Applying the existing
rank-two adjacent structure theorem on both sides shows that \(R/U\) is
irreducible and that \(P\) has a unique nonzero proper subrepresentation.
It also identifies the actual normalized Jacquet module of \(R/U\) with
the ordered tensor \(A\otimes B\).

That tensor is irreducible and cuspidal by the existing actual tensor
theorem. Its occurrence in the Jacquet module of \(R/U\), together with
the lower admissibility theorem for irreducibles and first adjunction,
gives an actual injection \(R/U\to P\). Its image is nonzero because the
source is simple and the map is injective. The image is proper because a
surjective injection would make \(P\) simple. Uniqueness therefore
identifies the image with \(S\).

`injectionRangeEquiv` constructs the actual source-to-image equivalence
of an injective intertwiner using the inverse onto its linear range.
The generic theorem `nonempty_equiv_uniqueProper_of_injective` packages
the preceding simple-source and unique-image argument for any topological
group, without an admissibility or finite-length hypothesis.

Finally, `decreasingProper_exists_increasingProper` shows that supplying
a proper \(S\subset P\) already ensures a proper \(U\subset R\): the
reducibility swap and the existing adjacent structure theorem produce it.
The equivalence theorem can then be applied to that actual \(U\). Thus
using the pair of results adds no hypothesis that a proper subspace of
the increasing product was supplied in advance.

This is an internal comparison within the local triple task. Its
provenance is the previously proved rank-two Jacquet and unique-subspace
structure, lower irreducible-product commutativity, actual tensor
cuspidality and first adjunction. It does not establish irreducibility of
either triple product or prove a Jacquet transfer. It does not use the
separate analytic adjacent-product reducibility conclusion.

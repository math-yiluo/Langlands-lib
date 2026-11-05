# Transport for geometric irreducibility spreading

These are internal auxiliary comparisons for the generic spreading
proof. They use Mathlib's actual scheme morphisms, fibres, restrictions, and
isomorphisms, with no additional literature assertion.

A point whose image under an inducing map is generic for the whole target
is generic for its own space, because inducing maps reflect specialization.
Geometric irreducibility is preserved by isomorphism of arrows. For a
pullback square, Mathlib's comparison of residue-field fibres expresses the
new actual fibre as a base change of the original fibre at the image point.
Stability under base change supplies geometric irreducibility of the new fibre.

An isomorphism of arrows restricts over corresponding target opens. The
source opens agree by commutativity; the restricted isomorphisms of source
and target form the resulting arrow isomorphism.

Finally, the affine empty-neighbourhood lemma is transported from spectra to
arbitrary affine schemes via their canonical global-section isomorphisms.
The generic point maps to a whole-space generic point and remains outside
the image. A kernel element supplied by the spectrum lemma defines the
required open neighbourhood, whose inverse image is empty.

A nonempty open part of an actual generic fibre remains geometrically
irreducible. A pullback-pasting isomorphism identifies that fibre with the
open subscheme obtained by pulling back the original source open immersion.
Its nonemptiness makes its morphism to the residue-field spectrum surjective,
so Mathlib's open-subscheme invariance applies.

For a quasi-compact source and an affine target, the empty-neighbourhood
argument also applies when the source is not affine. Choose a finite affine
open cover of the source, shrink separately for every cover member, and take
the finite intersection of these neighbourhoods. A point in the resulting
preimage would lie in a cover member whose preimage is already empty.

Geometric irreducibility over an open neighbourhood persists over a smaller
open neighbourhood. The proof restricts twice and identifies the resulting
arrow with the single restriction, using the inclusion of opens.

An isomorphism of arrows also transports the actual geometrically irreducible
fibre at a point to the fibre at the corresponding point. The inverse target
isomorphism gives a pullback square, and the fibre base-change comparison
applies. Equality of the corresponding point with the original point is
transported explicitly, since the fibre morphism depends on that point.

Finally, any two source opens meeting the geometrically irreducible generic
fibre intersect in that fibre. The original fibre has irreducible underlying
space over its field spectrum. Its inclusion has precisely the set-theoretic
fibre as range, so irreducibility of this image gives the intersection point.

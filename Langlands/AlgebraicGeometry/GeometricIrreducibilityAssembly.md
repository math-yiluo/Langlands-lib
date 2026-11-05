# Finite-cover assembly for generic geometric irreducibility

These internal helper lemmas assemble the scheme part of the proof of generic
geometric irreducibility spreading. They are derived from Mathlib's actual
fibres and restrictions and the accompanying scheme transport lemmas.

The image of a restricted morphism is the original image intersected with
the target open. A geometrically irreducible actual fibre is nonempty, so
its base point lies in the original morphism's image.

For two source opens meeting the geometrically irreducible generic fibre,
irreducibility of that fibre gives a common point. Choose an affine
neighbourhood of this point inside the intersection. Its actual generic
fibre remains geometrically irreducible. Assuming affine generic spreading,
this affine piece becomes geometrically irreducible, hence surjective,
over a neighbourhood of the base generic point. Its points give common
points of the original two opens in every fibre over that neighbourhood.
This conditional helper does not itself prove the main spreading target.

For a quasi-compact source over an affine base, choose a finite affine open
cover. Members meeting the generic fibre spread by the assumed affine
assertion. A member missing the generic fibre disappears over a
neighbourhood by the affine empty-neighbourhood lemma. The preceding overlap
lemma supplies a further neighbourhood for each pair of members meeting the
generic fibre. Intersect these finitely many neighbourhoods. The surviving
members cover the restricted source, are geometrically irreducible, and
have pairwise intersection in every fibre. The geometric open-cover
criterion proves the restricted morphism geometrically irreducible. No
quasi-separatedness hypothesis on the source is used.

Finally, for an arbitrary target, restrict to an affine open neighbourhood
of its whole-space generic point. That point is generic in this open,
the new actual fibre is a base change of the original one, and
quasi-compactness of the morphism gives a quasi-compact source over this
affine base. Apply the finite-cover argument and identify the double
restriction with the original morphism restricted to the image open.
The last lemma proves the exact published proposition conditionally on
affine spreading; the algebraic reduction module supplies this affine premise from the ring theorem.

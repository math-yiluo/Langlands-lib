# Rigidity of smooth connected group monomorphisms over a connected base

This internal construction proves that a monomorphic homomorphism between
smooth affine group families with geometrically connected fibres over a
connected scheme is an isomorphism if it is so on one supplied field fibre.
It is intended for the global dynamic Borel presentation in Task 6490.

The existing open isomorphism locus detects invertibility on every actual
field fibre: a field-fibre isomorphism extends to a base open by the
published smooth isomorphism-neighbourhood theorem, and membership in the
open locus makes every pullback with image in that locus invertible.

On any affine chart, this locus equals equality of the relative Lie ranks.
Both ranks are locally constant. The equivalence uses the published theorem
that a monomorphic homomorphism of smooth connected affine groups over a
field is an isomorphism when their Lie dimensions agree. Canonical
pullback comparisons retain the supplied field-valued morphisms.

The complement of the locus is open by checking on affine open charts, so
the locus is clopen. One field-fibre isomorphism makes it nonempty;
connectedness makes it the whole base. Reflection along the identity base
map gives invertibility of the original homomorphism.

`isoOfFieldIsoOfConnected` is the resulting concrete group isomorphism,
constructed with the original homomorphism as its forward map. No
noetherian, reducedness, separatedness or characteristic condition is added.

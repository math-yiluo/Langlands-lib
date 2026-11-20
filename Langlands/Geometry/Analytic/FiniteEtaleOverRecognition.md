# Finite étale models of a strong étale morphism

`StrongEtaleLocallyFiniteEtaleStatement` says that an actual strong map
which is étale over all recognized pieces admits a finite étale model
around each source point. The field, space and atlas-index universes
are independent. The companion theorem `strongEtaleLocallyFiniteEtale`
proves the statement for complete ultrametric normed fields, including
trivially normed fields.

The proof starts with the finite open neighborhoods supplied by the
pointwise flatness condition. More generally, it proves that every finite
model with open source for such a map has algebraically finite étale
bounded maps on all of its recognized inverse-image pieces.

Fix a point in one such piece. Shrink the point's all-pieces étale model
inside the original open source and choose a common recognized base
subpiece. The smaller source model is a clopen part of the original
inverse image over the common base. Its bounded restriction is flat and
surjective. The induced homomorphism of local rings at the relevant
kernel primes is surjective, flat, and local, hence bijective. After
transporting over the base algebra, this reflects pointwise étaleness
from the clopen piece to the full inverse image over the common base.
The nested recognized pullback comparison, with the published domain
flatness and finite tensor comparison theorems, reflects it to the
original piece.

The complement of the algebraic étale locus of a finite affinoid map is
closed in the prime spectrum. If it were nonempty, its defining ideal
would be proper and the bounded-spectrum ideal criterion would supply a
bounded point in the complement. Pointwise étaleness rules this out,
so the bounded map is algebraically finite étale.

This is an internal derivation from the Library's actual recognized
pieces, the prime-local pointwise criteria and the finite neighborhood
conditions. The resulting local models supply an input for descent of
localized analytic morphisms along étale covers.

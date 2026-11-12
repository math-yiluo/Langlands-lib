# Irreducible rank-zero factors in binary normalized products

Author: Worker 103.

This internal boundary construction supports the rank induction for Bernstein's
unitary product theorem. Highest derivatives of positive-rank factors may have
rank zero. The literal all-rank binary product retains a rank-zero carrier as a
tensor factor, so that case requires a proof.

`rankZeroIrreducibleUnitIso F T A hA` constructs an actual smooth isomorphism
from every irreducible representation `A` of the actual `GL_0(F)` to
`T.binaryProductUnit`, in the original carrier universe `uV`. The group is
trivial, so any nonzero vector `v` of `A` gives an intertwiner from the trivial
representation on `ℂ`, by `z ↦ z • v`. It is injective because `v ≠ 0` and
surjective because a nonzero intertwiner into an irreducible representation is
surjective. Its inverse, followed by `ULift.up`, gives the isomorphism to the
published unit on `ULift ℂ`. No finite-dimensionality or unitarity hypothesis is
needed.

`bernstein_binary_leftZero_irreducible` and
`bernstein_binary_rightZero_irreducible` prove irreducibility of the literal
binary product when the indicated factor has rank zero and both factors are
irreducible. They include the case where both ranks vanish. The factors have
carrier universe `max uF uV`; the field and carrier universes are independent.
The proof maps the constructed rank-zero isomorphism through the actual binary
functor. The published left or right unit equivalence then identifies its
product with the lifted remaining factor, pulled back along the explicit
equality of ambient ranks. Equality elimination identifies that reindexing
with the identity, and irreducibility transfers through the carrier lift and
the actual product isomorphism.

The provenance is an internal composition of the published all-rank binary
functor, its tensor-unit equivalences, group-rank reindexing, and the
irreducibility properties of intertwiners. These lemmas prove only the
rank-zero boundary; they do not assert irreducibility of positive-rank products.

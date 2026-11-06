# Regular spans of irreducible Frobenius products

Worker 669 derives this construction from the existing actual regular
representations, coordinate products, singleton regular spans, and Mathlib
linear algebra. No external structural existence theorem is used.

For actual matrix representations over a field,
`Intertwines.isIrreducible_of_bijective` transfers irreducibility along a
bijective intertwiner. The inverse image of a subspace stable on every
affine test is stable. The source's irreducibility makes this inverse image
zero or the whole source, and bijectivity reflects those alternatives back
to the target subspace. Injectivity also transports nontriviality.

The two inclusion-coordinate lemmas require only subspaces of a commutative
algebra over a field, finite bases, and a subspace inclusion. The retraction
identity identifies the existing `coactionCoordinates` with the matrix of
that actual inclusion. The standard matrix-coordinate formula then computes
the inclusion of every vector.

Let `G` be an actual group over `Spec k` with affine structure morphism,
in arbitrary universe `u`. Supply a finite regular coordinate subspace `V`,
a finite basis, and stability under every right contraction in its actual
coordinate coalgebra. If its actual regular representation is irreducible
on every affine test, every finite nonzero regular subspace `W` contained
in `V` equals `V`. The existing inclusion intertwiner has stable image.
Irreducibility makes its image zero or the whole coordinate space; the
inclusion-coordinate formula rules out zero using `W`'s nonzero premise
and converts surjectivity into the reverse inclusion.

`affineCovariantSocle_eq_of_mem_of_isIrreducible` applies this argument to
the existing singleton regular span `affineCovariantSocle G f`. Its leastness
among regular subspaces containing `f` gives containment in `V`, and `f != 0`
gives nonzeroness. Thus every nonzero coordinate in an irreducible finite
regular space generates that space. This argument needs no product cell,
unipotence, covariance, characteristic, or geometric reducedness hypothesis.

For the remaining constructions let `k` be a perfect field of exponential
characteristic `p` and let `G` also be reduced. Supply two finite regular
coordinate subspaces `V,W`, finite bases, their right-contraction stability,
and a natural number `e`. Write `q = p^e`. Assume the actual tensor

`(affineRegularRepresentation G V bV hV).tensor
  ((affineRegularRepresentation G W bW hW).frobeniusPower p e)`

is irreducible, and supply `v in V`, `w in W` with `v * w^q != 0`.
The existing multiplication matrix onto
`V * frobeniusCoordinateSpan p e W` is surjective, and the earlier
irreducible-source argument makes it injective. Its actual all-test
intertwiner and the general transfer lemma therefore make the regular
representation on this product irreducible for every supplied product basis
and right-contraction stability proof.

Choosing a finite basis of the product and using its proved regular
stability, the nonzero-coordinate generation theorem gives

`affineCovariantSocle G (v * w^q) = V * frobeniusCoordinateSpan p e W`.

In particular, take `V = affineCovariantSocle G f` and
`W = affineCovariantSocle G g`, with their constructed finite bases and
stability proofs. `affineCovariantSocle_mul_pow_eq` gives the corresponding
equality under the explicit irreducibility premise for the tensor of the
two actual `affineCovariantSocleRepresentation`s and the explicit nonzero
premise `f * g^q != 0`.

`frobeniusSocleProductEquiv` composes the existing multiplication equivalence
onto the product image with this equality. Its domain is the full tensor
product of the first singleton regular span with the Frobenius-powered span
of the second, and its target is the singleton regular span of `f * g^q`.
On pure tensors its value is actual coordinate multiplication. The dimension
formula follows from this equivalence, the tensor-product dimension formula,
and the powered basis, which has the same finite indexing as the original
second span.

All representation irreducibility and intertwining statements retain every
affine test algebra, including nonreduced test algebras. Reducedness concerns
`G` and is transported to its coordinate algebra to construct the powered
basis. Tensor irreducibility and the nonzero product remain supplied premises.
The result concerns generated regular subspaces; it does not identify them
with an entire covariance space or construct the geometric data required by
`SteinbergBigCellStatement`.

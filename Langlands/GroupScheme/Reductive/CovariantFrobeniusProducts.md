# Multiplication with Frobenius-powered regular coordinates

Worker 669 derives this construction from the existing coordinate-product,
regular-representation and Frobenius-coordinate constructions, together with
Mathlib linear algebra. Its proofs use no external structural existence result.

For subspaces `V,W` of a commutative algebra `B` over a field `k`,
`coordinateProductToSubmodule V W` is the multiplication map from the full
tensor product `V tensor W` to the product subspace `V * W`.
Its coercion to `B` is the existing `coordinateProduct` and it is surjective,
by that map's existing image description. These algebraic statements require
no group or characteristic hypothesis.

Given finite bases of `V,W` and `V * W`, `productMatrix_eq_toMatrix` identifies
the existing product matrix with this map in the tensor-product basis. The
proof applies the retraction identity on the product subspace to each basis
product. `productMatrix_mulVec_equivFun` computes the coordinates of every
tensor's product. Consequently the matrix is always surjective onto the
coordinate space of the product subspace. Matrix injectivity implies
injectivity of `coordinateProduct` on the full tensor product, and a single
nonzero product of elements of `V,W` makes the matrix nonzero.

For any actual matrix representations over a field, the kernel of an
`Intertwines` matrix is stable on every affine test, since it is the inverse
image of the zero stable subspace. `Intertwines.injective_of_isIrreducible`
uses the existing all-affine-tests `IsIrreducible` condition on the source:
its stable kernel is zero or everything, and the latter would make the map
zero. Thus an explicitly nonzero intertwiner is injective. This step needs no
affineness, reducedness or algebraic closure of the group.

Now let `k` be a perfect field of exponential characteristic `p`, and let `G`
be an actual affine reduced group scheme over `Spec k`, in arbitrary universe
`u`. Supply finite coordinate subspaces `V,W`, finite bases `bV,bW`, and
stability under every right contraction in the actual coordinate coalgebra.
Set `q = p^e`. The product of `V` and `frobeniusCoordinateSpan p e W` is again
regular. `frobeniusProductMatrix` is the existing multiplication matrix with
the powered basis of the second subspace and a supplied basis of the product.

`intertwines_affine_frobeniusProductMatrix` proves that this matrix
intertwines the actual representation

`(affineRegularRepresentation G V bV hV).tensor
  ((affineRegularRepresentation G W bW hW).frobeniusPower p e)`

with the actual regular representation on `V * frobeniusCoordinateSpan p e W`.
It starts with the existing multiplication intertwiner and replaces the
regular representation on powered coordinates with matrix Frobenius, using
their affine-matrix equality. The conclusion holds on every affine test
algebra, including nonreduced test algebras; reducedness concerns `G`.

If this actual tensor representation is supplied as `IsIrreducible` and there
are `v in V`, `w in W` with `v * w^q` nonzero, the multiplication matrix is
injective. Choosing a finite basis of the product gives injectivity of
`coordinateProduct V (frobeniusCoordinateSpan p e W)` without supplying product
coordinates. `frobeniusCoordinateProductEquiv` is then the linear equivalence
from the full tensor product of `V` with the powered coordinate span onto the
product subspace. Its value on a pure tensor is the coordinate product.
Surjectivity is onto that product subspace, rather than a larger covariance
space. The counit-normalized injectivity corollary supplies the nonzero-product
premise from coordinates `v,w` whose counits are both one: their product has
counit one by multiplicativity and hence cannot be zero.

Finally, for an actual morphism `i : H -> G` of groups with affine structure
morphisms, if `V` has covariance coordinate `chi` and `W` has coordinate `psi`,
then `V * frobeniusCoordinateSpan p e W` is contained in the covariance subspace
of coordinate `chi * psi^q`. This containment follows directly from covariance
multiplication and power containment and requires no characteristic,
perfectness, reducedness or group-like premise on the coordinates.

Tensor irreducibility remains an explicit premise. This unit does not construct
Steinberg modules, identify an entire induced covariance space with the product,
or prove the general `SteinbergBigCellStatement`.

Integration gives the local instances used here module-specific names to permit
joint imports. Their types, values, and local scopes are unchanged.

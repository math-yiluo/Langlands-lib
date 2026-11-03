# Linear coordinates for arbitrary torus actions on vector groups

`TorusVectorActionLinearizationStatement` is a proposition target over
every field in universe `u`. Given an actual torus `T`, a vector group `V`
of specified dimension `n`, and an actual automorphic action of `T` on `V`,
it asks for natural vector coordinates of the same dimension in which the
action is linear. The torus need not be split, and `n = 0` is allowed.

The input `IsVectorGroupOfDimension V n` gives group equivalences between
`V`-points and `n` global functions on every scheme over the field,
natural under all test morphisms. The output uses the existing
`IsLinearVectorCoordinates`: it includes that naturality and requires the
actual action of every torus point to commute with multiplication by
every global function on the same test. Additivity follows from the
automorphic action and the group equivalences. Thus the action is linear
over the actual ring of global functions on every test, including
nonreduced tests. Several weights and the zero weight are allowed.
The output may choose different coordinates from those witnessing the
input vector-group predicate.

This is a derived consequence of Conrad–Gabber–Prasad,
*Pseudo-reductive Groups*, second edition (2015), registered as
`conrad-gabber-prasad-2015-pseudo-reductive`, SHA256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
In characteristic zero, A.1.1, printed p.466 (PDF p.492), records the
unique linear structure on a vector group and linearity of all
homomorphisms. The algebraic action respects that structure; verifying
this as a scheme identity gives the all-test condition.

In positive characteristic, Theorem B.4.3, printed p.577 (PDF p.603),
applies to any torus, not only a split torus. It decomposes a smooth
commutative group killed by the characteristic into its fixed subgroup
and a complementary vector subgroup with a linear torus action. Applied
to the vector group `V`, its fixed factor is also a vector group. Indeed,
the product decomposition gives an algebraic group projection from `V`
onto the fixed factor. Over a separable closure, compose the coordinate
affine lines in `V` with this projection. Their images generate the
fixed factor, so Proposition B.1.11, printed p.566 (PDF p.592), makes
that factor a vector group. This also follows by projecting arbitrary
affine-line morphisms through the identity. Give it any linear structure:
the torus acts trivially on it. Combining this with the linear structure
on the moving factor supplies the desired one on `V`.
Proposition B.4.2, printed pp.576–577 (PDF pp.602–603), supplies the
equivariant linear decomposition used by B.4.3.

The source decomposition is not a claim that every smooth subgroup of
a vector group over an imperfect field is a vector group. The fixed
factor here is a retract of the given vector group, which is what
supplies the affine-line generation used above. No chosen linear
structure on the input is asserted to be preserved.

A proof must compare the all-test vector-group predicate with an actual
isomorphism to the standard vector group, implement the source
decomposition or another valid linearization argument, retain dimension
`n`, and establish the stated identity on every scheme test. The source's
geometric-point descriptions alone do not discharge those obligations.
The statement has no perfection, infinitude, algebraic-closedness, or
characteristic restriction and introduces no conjugacy premise. This
file proves neither the linearization target nor maximal-torus conjugacy.

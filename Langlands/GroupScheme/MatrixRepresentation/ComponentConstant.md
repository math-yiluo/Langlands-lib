# Componentwise constant matrix representations

Let `G` be a group scheme locally of finite type over an algebraically closed
field `k`. A rational matrix homomorphism `G(k) → GL(n,k)` that is constant on
the actual connected components of `G` defines an actual matrix representation.
The construction `ofComponentConstantRationalMatrix` uses the equivalence
between rational points of the actual general linear group scheme and
ground-field invertible matrices, followed by `ofRationalGroupHom`.
Its rational matrices equal the prescribed matrices.

For every componentwise constant representation, `pointMatrix_component`
identifies its matrix on an actual open component scheme with scalar extension
of its matrix at a rational representative of that component.
Consequently, rational matrix identities expressing coordinate stability hold
on every component scheme. The separatedness of global sections glues these
identities over the open component cover, proving stability on every scheme
test. This does not assume that the group scheme is reduced.

For a vector subspace, choose split coordinates and apply the coordinate
criterion. The resulting actual restricted representation identifies its range
with the original subspace, proving all-affine-test coefficient stability.
For affine `G`, the converse follows from the published rational matrix
invariance lemma for all-test stable subspaces. The final theorem
`isStableSubspace_ofComponentConstantRationalMatrix_iff` states that the
constructed representation's all-test stable subspaces are exactly those stable
under the prescribed rational matrices.

This is internal derived infrastructure for the regular representation of a
finite component group in Nagata's theorem. It uses actual component gluing
and restriction of global sections; equality on rational points is used only
for maps already proved componentwise constant. The construction needs no
smoothness or reducedness assumption.

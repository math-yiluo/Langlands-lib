# Galois-permuted finite families of standard parabolics

This internal unit constructs the actual intersection used in a finite-family
parabolic descent argument. The ground fields and group schemes have arbitrary
universe `u`; the finite family can have a separate index universe `v`.

The subgroup-functor lemmas first prove that taking a preimage and applying
the canonical Galois transport commute with arbitrary all-test intersections.
If a Galois automorphism permutes the members by a supplied bijection of
indices, the intersection is invariant. This follows by reindexing the
universal membership condition with the inverse bijection.

For a connected reductive group, a maximal split torus and a generic
cocharacter, `mem_standardParabolic_finsetInf` identifies membership in a
finite standard intersection with membership in each member. Its root index
is the intersection of all the specified simple-root subsets, intersected
with the full simple-root set. This normalization also handles an empty
family, for which the group is the full-group standard parabolic. The proof
inducts over a finite set and uses the binary all-test intersection theorem.

`Standard.finiteParabolicIntersectionHom` is the original canonical standard
inclusion for that index. Its all-test range is the family intersection,
and it is parabolic by the published standard-cocharacter and dynamic
recognition theorems. Applying one ambient group-scheme isomorphism to this
inclusion gives the intersection of the identically transported original
member inclusions. The isomorphism can in particular be a rational inner
automorphism.

The final theorem
`IsMaximalSplitTorus.eq_simpleRelativeRoots_of_galoisPermuted` adds a central
maximal split torus in the ground-field connected reductive group. Over a
Galois extension, it takes a finite family of standard parabolics and one
ambient isomorphism. Its essential additional premise is that every Galois
automorphism permutes the all-test ranges of those transported inclusions.
The preceding lemmas make the actual intersection invariant. The published
Galois-invariant-parabolic theorem makes its inclusion an isomorphism.
Removing the ambient isomorphism shows that its standard range is the whole
group. The standard-parabolic order theorem forces its root index to be the
full simple-root set; therefore every member index is that full set.

All hypotheses on connected reductivity, maximal splitness and genericity
are retained explicitly. The final theorem takes connected reductivity of
both the ground group and its scalar extension. For an algebraic Galois
extension, the published ascent theorem supplies the latter from the former.
The family-permutation premise is not proved here. In particular this module
does not derive it from adelic overlap estimates, prove root bounds or
fundamental coverage, or establish the full adelic compactness theorem.

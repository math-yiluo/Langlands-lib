# Comparing semisimple Galois representations by Euler polynomials

For a Galois extension, the chosen closure isomorphism identifies the image
of absolute Galois restriction with the pointwise fixing subgroup of a
transported Galois intermediate field. This subgroup is normal. The Library's
finite-dimensional normal restriction theorem preserves semisimplicity on
that subgroup. The pullback has the same set of acting endomorphisms as the
restriction to the subgroup, so it is also semisimple. For a surjective field
map the image is the whole group and the same argument applies.
[Closure comparison](Local.md), [normal restriction](../../Representation/Category/NormalRestrictionSemisimplicity.md)

For two semisimple representations over a Hausdorff topological field of
characteristic zero, `equiv_of_eventually_hasEulerPolynomialAt` takes a common
Euler polynomial at each place outside a finite set. Unramifiedness gives the
same polynomial for every actual geometric Frobenius lift at such a place.
The coefficient of degree one in the Euler polynomial is the negative trace,
so the characters agree on the images of these lifts in the global absolute
Galois group. Conjugacy invariance gives agreement on their conjugates.
The Library density theorem makes this set dense, and continuity into the
Hausdorff coefficient field extends the equality to the whole group.
Character rigidity then supplies a linear intertwiner.
[Density of actual geometric Frobenius conjugates](../AbsoluteGeometricFrobeniusDensityProof.md), [character rigidity](CharacterRigidity.md)

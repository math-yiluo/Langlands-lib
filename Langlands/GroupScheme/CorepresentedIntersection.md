# Closed intersections in corepresented affine groups

For a family of subgroup functors on a group scheme, `SubgroupFunctor.intersection` takes the intersection of their subgroups on each test scheme. The index may be empty. Restricting a point preserves membership in every member of the family.

For a corepresented affine group over an arbitrary commutative ring, suppose each member is cut out on affine tests by an ideal of the coordinate algebra. `Corepresented.isAffineCutOutBy_intersection` identifies the intersection with the vanishing of the sum (the supremum) of those ideals. Its proof uses the kernel of the classifying ring map: it contains the sum exactly when it contains every summand.

`intersectionScheme` and `intersectionHom` apply the existing quotient-algebra group construction to this ideal sum. The inclusion is a closed immersion and represents the intersection on every test scheme, including nonaffine and nonreduced schemes, by the existing affine-to-all-tests reduction. No finiteness, field, smoothness, connectedness or reductivity premise is needed or asserted.

This is an internal construction derived from `Dynamic.Representability` and `CorepresentedClosedSubgroup`. It supplies a reusable ideal-sum construction for intersections of the explicit dynamic subgroup ideals; it does not assert that every arbitrary subgroup functor is ideal-cut.

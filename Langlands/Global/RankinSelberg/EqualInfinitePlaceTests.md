# Local equal-rank tests at the infinite places

`RealEqualPlaceTestsStatement` and `ComplexEqualPlaceTestsStatement` express
the test existence obligations at a single place of a number field. They
retain the compact additive adelic quotient, the unitary adelic character
trivial on the number field, the cuspidal pair and its contragredients, and
the specified local characters and representation parameters from the
equal-rank target. A test consists of two actual place restrictions for
the opposite characters, one local Schwartz function, and compatible
quotient measure data. Its ordinary and dual integral each must be
holomorphic on a right half-plane and have one nonzero value there. The
two half-planes and evaluation points may differ.

`HolomorphicNonzeroOnRightHalfPlane.exists_ne_zero_above` uses the
holomorphic identity theorem on the open convex half-plane of holomorphy.
If the function vanishes everywhere to the right of a given bound, it
vanishes on a neighborhood of a point in the original half-plane. The
identity theorem then contradicts the given nonzero value. For two such
functions, first take a point in their common half-plane where the first
function is nonzero. It stays nonzero near that point. If the product
vanishes throughout the common half-plane, the second function vanishes
on that neighborhood, again a contradiction. Induction gives the same
conclusion for a finite product, with the empty product equal to one.

`infiniteTestData_of_local` chooses the actual local witnesses place by
place, then applies the product argument to the ordinary integrals and to
the dual integrals using the same tests. This gives both nonvanishing
clauses of `EqualInfiniteTestData`. The scalar field of that structure
is set to one until the Whittaker product supplies its normalization.
The product result is internal complex analysis on the Library's
integrals. The existence of each local test is the premise.

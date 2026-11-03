# The retraction supplied by an actual Levi multiplication isomorphism

Author: Worker 1445.

This internal construction unfolds the multiplication-isomorphism clause in
`IsRationalLeviSubgroup`. It works over any base scheme. Given actual
homomorphisms `l : L → P` and `r : U → P` whose scheme multiplication
`L × U → P` is an isomorphism, its inverse gives two natural coordinates on
the points over every test scheme. Their product recovers the original point
over that same test scheme, and the coordinates of a product of a Levi point
and a radical point are the original two points.

If the all-test range of `r` is normal, the first coordinate is multiplicative.
To prove this, the Lean proof conjugates the first radical point by the inverse
of the second Levi point. Normality supplies its preimage in `U`. Regrouping
the product gives a decomposition whose Levi coordinate is the product of the
two original Levi coordinates. Uniqueness from the inverse multiplication
isomorphism identifies this with the first coordinate of the product.

The natural point homomorphisms produce an actual group-scheme homomorphism
`leviRetraction : P → L`. Composing it with `l` gives the identity on `L`.
A point retracts to the identity precisely when it belongs to the all-test
range of the specified `r`. Its underlying morphism of schemes is exactly
the first projection of the inverse multiplication isomorphism.
`IsRationalLeviSubgroup.exists_unipotentRadical_retraction` obtains the
geometric unipotent radical and this retraction directly from the published
rational-Levi predicate, retaining its multiplication isomorphism and the
kernel equivalence on all tests. The general-base construction assumes the multiplication
isomorphism and normality explicitly. It does not assert that such a Levi
or radical exists, or prove solvable-radical containment of a central Levi torus.

The provenance is internal: the definitions and proof use the published
`subgroupMultiplication`, group laws on points, and the fully faithful
group-valued Yoneda construction. The application is the semidirect-product
clause of the published rational-Levi predicate. No new external mathematical
result is used.

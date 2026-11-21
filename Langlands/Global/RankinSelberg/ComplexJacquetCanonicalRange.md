# The exact complex Whittaker model from identity evaluations

`ComplexJacquetCanonicalRangeStatement` assumes
`ComplexJacquetIdentityProportionality`. This premise asks for the
identity evaluations of every Whittaker intertwiner to be proportional
to the canonical identity evaluations on the same standard K-finite
module. Under this premise, for any inducing list of the correct length,
the exact complex Whittaker model for the character of parameter \(-a\)
is the range of the canonical Jacquet linear map with Fourier parameter
\(a\). The scalar additive Haar measure can be chosen arbitrarily.

The proof reconstructs the inducing list from the angular weights and
radial exponents of its entries. The defining character formula gives
entrywise equality, which `List.ofFn_get` assembles into list equality.

For two intertwiners with proportional identity evaluations, the proof
subtracts the indicated scalar multiple of the second from the first.
The resulting family is smooth and real analytic in the open matrix
chart. It is stable under real right differentiation by the common
standard Lie action. Vanishing at the identity for every inducing vector
then gives vanishing of every matrix jet there. Analytic continuation on
the connected invertible matrices gives proportionality of the full
intertwiners. Each such intertwiner has range inside the canonical range
because its scalar can be applied to the inducing vector. The reverse
inclusion uses the verified canonical intertwiner itself.

This is an internal reduction of model identification. Jacquet,
*Archimedean Rankin–Selberg integrals* (2009), p. 4, uses uniqueness of
the continuous Whittaker form on the smooth induced representation.
Here the comparison of identity evaluations is the explicit premise
on the Library's compact-finite intertwiners.

# Nonidentity normalizers from distinct extreme weights

This internal construction removes the rational centralizer-containment premise
from the supplied-nonfixed-section construction in
`NonidentityNormalizerFromProperQuotient`. It is derived from existing Library
arguments and `FlagCore.centralizerSeparatedOrbitLines`; it introduces no
external structural assertion.

`nonidentityNormalizerOfWeightSeparatedProperQuotient` works over an algebraically
closed field of arbitrary characteristic. Its inputs are a maximal torus
`i : T → G`, a closed subgroup `j : P → G` containing that torus through a
specified factor, internal conjugacy of maximal tori of `P`, a flat, surjective,
quasi-compact quotient map to a proper scheme with exact all-test fibers,
an actual finite matrix representation with `P` as the exact all-test stabilizer
of a coordinate line, and a rational lift whose quotient section is not fixed
by the torus action on all tests. The ambient group is locally of finite type.
The output is an actual rational normalizer point whose class in
`N_G(T)(k)/Z_G(T)(k)` is nonidentity.

Properness gives a closed projective orbit. Torus diagonalization and the
nonfixed section give two actual extreme orbit lines separated under every
point commuting with the torus. Rational line fixedness becomes all-test
fixedness because the torus is smooth and the quotient is separated. Internal
maximal-torus conjugacy then corrects each extreme representative to a
normalizer representative `n₁` and `n₂` of the same quotient section.

The chosen point is `n₁ * n₂⁻¹`. If its Weyl class were the identity, it would
centralize the torus and hence all its rational parameters. Exact quotient
fibers give scalar proportionalities between each extreme orbit vector and
its corrected representative. Since `(n₁ * n₂⁻¹) * n₂ = n₁`, these yield a
scalar proportionality between the two extreme orbit vectors after applying a
centralizing point. This contradicts their separation. The proof uses the
product of the two scalar factors and performs no scalar division.

The construction does not assume that the whole torus centralizer lies in `P`.
It retains a supplied nonfixed section, the quotient and representation
geometry, and internal maximal-torus conjugacy. It does not establish existence
of such a section without further hypotheses, dynamic centralizer containment,
or the unconditional rank-one positive-root uniqueness statement.

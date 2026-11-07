# Rank-one JPSS coefficient integrals in scalar coordinates

This internal construction extends the existing p-adic coefficient-integral and
rational-value comparisons of `TateScalarFunctionalEquation` to an arbitrary
nonarchimedean local field. It uses the exact Haar transport in
`LocalTateTransport` and the existing actual character models, scalar Mellin
integrals, and JPSS equal-rank integrals. There is no characteristic-zero or
second-countability premise. Borel measurable structures are supplied on the
units, GL1 and its rank-one unipotent quotient; the field is Hausdorff.

`tateCoefficientTest` multiplies the scalar-coordinate row test by the values
of both coefficient functions at the identity. The first coefficient is for the actual
character representation of `χ`, with the identity functional, and the second
is for the trivial character with its identity inverse functional. The existing
coefficient formula gives the first coefficient at a scalar matrix as `χ(a)`
times its value at one, and the trivial coefficient is constant.

The integral comparison first removes the trivial rank-one unipotent quotient,
then applies exact scalar-to-GL1 Haar transport. At the scalar matrix `a`, the
determinant is `a` and the last row is the one-coordinate row with entry `a`.
The rank-one determinant weight is one, giving exactly the weight-one scalar
Mellin integral of the absorbed coefficient test. The same pointwise identities
and measure preservation identify absolute convergence with scalar
integrability, for both the original and dual coefficient integrands. For the
dual integral the rank-one long Weyl element is one, and inverse transpose inverts the determinant;
the same computation gives the inverse multiplicative character.

The coefficients of the unit model vectors have value one at the identity.
Consequently every scalar test is recovered by pulling it back to a row test
and taking these unit vectors. These two directions identify the full original
and dual rational-value sets, with all tests and coefficients quantified and
with no existence of continuations assumed. These are equalities of sets of
actual rational continuations, rather than an abstract isomorphism of ideals.

The provenance is internal coordinate and coefficient algebra using the
published constructions named above. The extension of the old p-adic
comparison uses only the general-field Haar transport. No analytic continuation,
normalized-generator, functional-equation, epsilon or conductor conclusion is
proved by this unit.

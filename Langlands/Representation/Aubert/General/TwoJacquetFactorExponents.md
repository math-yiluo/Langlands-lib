# Full-center exponents of the two actual induction factors

This is an internal data structure and deduction from `InductionTwoJacquetFactors`, scalar
full-center actions and the published definition
`HasStrictNormalizedJacquetExponents`. It introduces no assertion from
external literature.

`InductionTwoJacquetScalarCharacters` is a defined type bundling two
multiplicative characters and their actual scalar-action proofs. Its
`first` character is defined on the full abstract center of the inducing
Levi and acts on the inducing representation. Its `second` character is
defined on the full abstract center of the other Levi and acts on that
Levi's normalized Jacquet module of the whole normalized induction. The
two Levi subgroups may differ. The structure assumes these scalar actions;
it does not construct them or assert open kernels. Each rational-point
factor lemma takes this same structure and tests its corresponding character.

The generic lemmas work over arbitrary group and representation universes.
`not_isCentralExponent_of_subsingleton` shows that a zero representation has
no exponent: every generalized central-character space is the zero subspace.
`InductionTwoJacquetFactors.subspace_centralExponent_eq` embeds the first
Jacquet module of the actual subspace into the inducing scalar action using
the factor's inducing equivalence.
`InductionTwoJacquetFactors.quotient_centralExponent_eq` uses the inverse of
the second quotient equivalence to embed the second Jacquet module of the
actual quotient into that of the whole induction. The published
`centralExponent_eq_of_scalar_injective` identifies the character in both
cases. These conclusions concern actual full abstract centers and retain
the open-kernel condition in the definition of a central exponent.

The rational-point lemmas use the actual standard parabolic, Levi and
radical subgroups. The field has arbitrary universe `u`, and the
representation universe is `max (u + 1) v`. They assume a finite actual
simple-root type, compact-limit radicals, actual two-factor and scalar-character data, and
vanishing of the whole induction's Jacquet modules at proper indices
outside the two selected indices. The full-index case is treated
separately: the explicit `hfull` premise says that a torus point mapping to
the full-index Levi's center cannot be a noncentral negative test point.
In particular, the lemmas do not assume that the full-index Jacquet module
vanishes.

For the subspace, a strict bound on `C.first`, the inducing scalar character at the
first index implies `HasStrictNormalizedJacquetExponents` for that literal
subspace. For the quotient, a strict bound on `C.second`, the scalar character of the
whole induction's second Jacquet module implies the same condition for the
literal quotient. Each proof splits the test index into the surviving
index, the other selected index, the full index and the remaining proper
indices. Scalar character identification handles the first case.
The factor's asymmetric Jacquet vanishing handles the second case,
`hfull` excludes the third, and exact Jacquet inheritance excludes the
remaining cases.

The existence of the factor datum, the proper-index vanishing, the
full-index exclusion, the scalar character of the second whole-induction
Jacquet module and both scalar character bounds remain inputs. This file
does not prove a sign trichotomy, square-integrability sufficiency,
self-association, or the exact rational rank-one target.

# Spherical Hecke operators on invariant restrictions of automorphic forms

## Invariant restrictions and eigenforms

`AutomorphicInvariantCondition K n` is a named abbreviation for
`Subrepresentation (continuousRightAction K n)`. For any condition `S` at
rank `r + 1`, the module
constructs `RestrictedAutomorphicSphericalVectors`,
`restrictedAutomorphicSphericalHeckeAction`, and
`restrictedAutomorphicStandardHeckeOperator` on the existing
`RestrictedAutomorphicForms` space. The same topology transport proves
smoothness. The zeroth operator is again the identity.

`restrictedAutomorphicSphericalInclusion` is the existing local intertwiner
restricted to fixed vectors. It is injective, and
`restrictedAutomorphicSphericalInclusion_heckeAction` proves naturality for
every element of the whole spherical corner using
`Hecke.cornerAction_intertwiner`. The standard-operator identity is its
specialization. Thus these constructions apply in particular to the existing
central-character subrepresentation, the cuspidal subrepresentation, and
their intersection. The cuspidal choices retain the existing
`CompactSpace (AdeleQuotient K)` hypothesis of those constructions; this
module does not prove quotient compactness.

`IsSphericalHeckeEigenform` requires a nonzero spherical form and simultaneous
scalar equations for every standard operator. For the multiplicity-preserving
multiset `s : Unramified.Eigenvalues (r + 1)`, the scalar is the existing
`Unramified.standardHeckeScalar`:

`(sqrt(q) : complex)^(i*(n-i)) * (-1)^i * s.eulerPolynomial.coeff i`.

Here `q` is the actual residue cardinality and the square root is the
nonnegative real square root embedded into the complex numbers.
`IsRestrictedSphericalHeckeEigenform` states the same nonzero relation in
the restricted space. `isRestrictedSphericalHeckeEigenform_iff` proves that
it agrees with the ambient relation under the actual inclusion, using
injectivity, naturality, and complex linearity.

## Internal provenance and scope

This module specializes the existing corner action and fixed-vector map to
actual invariant restrictions of automorphic forms. It imports the canonical
spherical action from `SphericalHecke`. Intrinsic proofs use topology transport,
fixed-vector injectivity, corner naturality and linearity. It makes no
irreducible-local-component, eigenform-existence or classification assertion.

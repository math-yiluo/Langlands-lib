# Finiteness of intertwiners and integral central operators

This internal module proves finite-dimensionality of the full algebraic
intertwiner space from a smooth representation that is finitely generated over
the group algebra to an admissible representation. Neither irreducibility nor
finite length is assumed. The group and the two complex representation carriers
have independent universes, and zero representations are allowed.

`fixedGeneratorEvaluation` evaluates each intertwiner on a supplied family of
vectors. For each vector a subgroup fixing it is supplied, and the corresponding
output lies in the target's fixed-vector space for that subgroup. This is a
complex-linear map to a dependent product of fixed-vector spaces.
`fixedGeneratorEvaluation_injective` assumes that the vectors generate the
source over the actual group algebra. It identifies intertwiners with
group-algebra-linear maps and applies linear-map extensionality on generators.

`finite_intertwiningMap_of_finiteType` chooses a finite family of group-algebra
generators. Smoothness of the source supplies an open stabilizer for each
generator. Admissibility of the target makes every corresponding fixed-vector
space finite dimensional. The finite product is finite dimensional, and the
injective evaluation map transfers that property to the full intertwiner space.
There is no need to choose a common compact open stabilizer.

`representationEndForget` is the complex-algebra homomorphism from endomorphisms
over the group algebra to the underlying complex-linear endomorphisms. It uses
the existing equivalence between group-algebra maps and intertwiners; composition,
identity and scalar endomorphisms are preserved.

`isIntegral_intertwiner_of_admissible_finiteType` applies the finiteness theorem
to an admissible finite-type representation as both source and target.
Transport through the intertwiner/group-algebra-map equivalence makes its
group-algebra endomorphism algebra finite over the complex numbers. Mathlib's
`IsIntegral.of_finite` gives a monic annihilating polynomial for each element of
that algebra. Mapping through `representationEndForget` gives the same
integrality assertion for the underlying operator on the whole carrier.

`isIntegral_centralAction_of_admissible_finiteType` applies this result to the
existing `Representation.IntertwiningMap.centralMul`, for a group element in
the monoid center. Consequently its action on the full representation satisfies
a monic complex polynomial. The polynomial is nonzero because its coefficient
field is nontrivial; this does not require a scalar central character.

The provenance is internal linear algebra using the published definitions of
smoothness, admissibility and fixed vectors, the Mathlib equivalence between
intertwiners and group-algebra-linear maps, finite generation, and integrality
of finite algebras. This is a prerequisite for the residual central-operator
argument in equal-rank trilinear uniqueness. It does not establish the spectral
support of bilinear forms or the full trilinear uniqueness theorem.

# Central directions in the represented-parabolic Casselman criterion

Author: Worker 1680.

This is an internal supporting derivation for the represented-parabolic
Casselman criterion. It uses the published normalized Jacquet quotient,
unitary central character, generalized exponent, normalized real-part and
compatible root-presentation constructions. It proves the central restriction
of normalized Jacquet exponents and the positive-cone clause for the identity
parabolic. It does not prove the criterion for proper parabolics or assert
the existence of a compatible presentation.

`normalizedJacquet_apply_of_unitaryCentralCharacter` concerns any locally
compact nonarchimedean group, closed radical subgroup and normalizing Levi
subgroup. At any Levi point that is central in the ambient group, the
normalized Jacquet representation acts by the prescribed ambient central
character. The proof lifts a vector through the surjective actual
coinvariant projection. The published
`normalizedJacquetFunctor_obj_apply_of_mem_center` says that the inverse
half modulus is one there. Apply the original central scalar action and
linearity of the quotient projection. No inclusion of the entire ambient
center in the Levi is assumed.

`normalizedJacquet_generalizedEigencharacter_apply_eq_centralCharacter`
then treats an arbitrary homomorphism from a group into that Levi. A
generalized eigencharacter provides one nonzero vector and a common
natural-number power. At a point with central ambient image, replace the
Jacquet operator by the scalar just established. Its power equation becomes
the scalar difference raised to that power, times the nonzero vector,
equal to zero. Over the complex numbers the difference must vanish, which
gives equality of the character values. Neither representation nor Jacquet
admissibility, finite length or a global weight decomposition is used.

`normalizedJacquetExponent_apply_eq_centralCharacter` specializes this to
the actual split-component map of an arbitrary represented parabolic.
`isNormalizedJacquetExponent_iff` converts the published exponent predicate
to the required uniform generalized eigencharacter. The corollary
`normalizedJacquetExponent_norm_eq_one_of_mem_center` applies the prescribed
unitarity of the central character.

Over any nonarchimedean local field,
`normalizedJacquetExponent_realPart_restrict_eq_zero` takes a morphism
`f : B ⟶ A` from any split torus into the Levi split component, with
ambient-central composite through the specified Levi and parabolic maps.
The exponent pulled back to `B` has modulus one at every rational point by
the preceding corollary. The all-point uniqueness theorem for
`normalizedRealPart` therefore gives zero for its parameter. The published
actual-morphism naturality of that parameter identifies it with the real
character pullback of the original parameter. This uses the `q^(-s)`
normalization already fixed in the criterion.

`ParabolicRootPresentation.positiveCone_identity` proves that every
compatible presentation of the identity parabolic and identity Levi has
positive cone exactly `{0}` in the full real character space. Its forward
inclusion uses the published containment in the nonnegative cone and
`nonnegCone_identity`. For the converse, take every coefficient equal to
one. The published `restrictedRoot_eq_zero_identity` makes each summand
zero. This also works for an empty root set.

Finally
`unitaryCentralCharacter_identityJacquetExponent_realPart_eq_zero` applies
the pointwise unitarity result to the central split component of the whole
group, using `normalizedRealPart_eq_zero_iff`.
`unitaryCentralCharacter_identityJacquetExponent_mem_positiveCone`
combines this with `positiveCone_identity`. It keeps any represented
geometric radical and matching multiplication isomorphism allowed in the
published exponent construction. It requires no nonzero-carrier premise:
if an exponent exists, its nonzero generalized vector is already part of
that predicate.

The field, representation and auxiliary group universes are independent.
The represented-parabolic lemmas use the canonical rational-point topology
over a Hausdorff topological field, an affine ambient group, and the local
compactness and nonarchimedean hypotheses already needed by the Jacquet
functor. Only the real-part lemmas add the local-field hypotheses. The cone
identity requires local finite type, and the last theorem obtains that from
connected reductivity. These are supporting lemmas, with no square
integrability, Cartan decomposition, Iwahori contraction or presentation
existence claimed.

`IdentityParabolicCasselmanConeStatement` packages precisely the universal
identity-parabolic clause just proved: every supplied split component,
geometric radical, multiplication isomorphism and compatible presentation
is allowed, and every normalized exponent lies in the positive cone for
each smooth representation equipped with a unitary central character.
`identityParabolicCasselmanCone` proves this proposition by the preceding
pointwise theorem. The statement has no admissibility premise and does
not contain either analytic implication for a proper parabolic.

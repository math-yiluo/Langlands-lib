# Inducing exponents of actual induction subrepresentations

This internal construction concerns the actual normalized induction and
Jacquet functors for a subgroup semidirect decomposition `P = M ⋉ U` in a
locally compact nonarchimedean group. The radical is closed and is a limit of
compact subgroups. The group and inducing carrier universes are independent;
the induced carrier and its invariant subspaces have universe `max uG uV`.

`subrepresentationJacquetInducingEquiv` assumes irreducibility of both the
inducing object and the actual inducing Jacquet module of its induction.
For every nonzero invariant subspace of the induction, it constructs an
actual representation equivalence from the Jacquet module of that subspace
to the original inducing object, even when their carrier universes differ.
The underlying map is first adjointness applied to the actual inclusion.
`subrepresentationJacquetInducingEquiv_mk` identifies it on each quotient
generator with evaluation of the included induced function at the identity.

The implemented proof first uses
`subrepresentationJacquetInclusionEquiv`, whose underlying map is Jacquet
restriction of inclusion. The published
`SmoothRep.isIrreducible_of_equiv` transports simplicity of the middle
Jacquet module to that of the subspace. The inclusion is nonzero because
the subspace is nonzero. Finally
`FirstAdjointness.equivalenceOfIrreducibleJacquet` turns its nonzero actual
adjoint into an equivalence between the two simple representations.
`isUnimodularModulus_of_isLimitOfCompactSubgroups` supplies the modulus
hypothesis of this actual first-adjointness construction.

`subrepresentation_jacquet_centralExponent_eq` additionally assumes a
specified scalar character of the full abstract center of the inducing
Levi. It proves that any `IsCentralExponent` of the subspace's inducing
Jacquet module is that character. It applies
`centralExponent_eq_of_scalar_injective` to the just-constructed actual
equivalence. The exponent uses the original open-kernel and uniform
generalized-space convention on the full abstract center.

No external literature assertion is introduced. The declaration-level
dependency on actual first adjointness is explicit above.
`subrepresentationJacquetInclusionEquiv` in turn uses actual compact-limit
Jacquet exactness and the nonvanishing consequence of that same
adjointness. No classification, character independence, geometric lemma or
cuspidal-support theorem is used. Neither finite length nor admissibility is
assumed. The simplicity of the middle Jacquet module and existence of the
displayed inducing scalar character remain inputs, as do the support
vanishing at other Levis, the sign of this character, square integrability,
unitarity and the exact `RationalRankOneSelfAssociationStatement`.

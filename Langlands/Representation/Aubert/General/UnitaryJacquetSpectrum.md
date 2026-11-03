# Conjugation of central exponents on actual unitary Jacquet modules

This internal algebraic development extends the published Hermitian Jacquet
carrier equivalence to the actual normalized Levi action and its uniform
generalized central-character spaces. It proves a same-subgroup comparison
with the smooth dual. Opposite-Jacquet duality and the rank-one
self-association theorem remain separate obligations.

`conjugateComplexCharacter` composes a complex unit character with complex
conjugation. Its kernel and every value's norm agree with those of the original
character. For a conjugate-linear equivariant map,
`conjugateLinearMap_action_sub_pow` proves by induction that the map takes each
power of an action operator minus a scalar to the corresponding power with
conjugated scalar. Thus a conjugate-linear equivariant equivalence preserves
the same finite uniform central exponent for every vector. Passing to the
increasing union gives an actual conjugate-linear equivalence
`conjugateGeneralizedCentralCharacterEquiv` of generalized central-character
spaces. The equivalence preserves vanishing; the unchanged open kernel then
gives `isCentralExponent_conjugate_iff`.

`star_closedInverseHalfCharacter` unfolds the actual Haar inverse half modulus
as the inverse of a positive real square root, embedded into the complex
numbers. Complex conjugation fixes it. On each actual coinvariant class
`unitaryJacquetConjugateEquiv_apply_action` uses that fact and the equivariance
of the Hermitian identification to prove equivariance for the normalized Levi
action. The quotient map is surjective, so this proves the identity on the
whole normalized Jacquet module.

`unitaryJacquetCentralCharacterEquiv` restricts this normalized equivalence
to each uniform generalized central-character space. Finally,
`unitaryJacquet_isCentralExponent_conjugate_iff` states the exact
same-subgroup central-exponent correspondence for any admissible unitarizable
smooth representation, using the actual smooth contragredient and the actual
Haar-normalized Jacquet functor. The group and carrier universes are independent;
no finite length, irreducibility or reductive specialization is required.

The provenance is an internal derivation from
`Langlands.Representation.Aubert.General.UnitaryJacquet`,
`Langlands.Representation.Exponents.Central` and their published imports.
The Hermitian identification uses finite-dimensional Riesz representation
only on compact-open fixed spaces, through
`Langlands.InvariantPositiveForm.smoothDualEquiv`. Compact-open cofinality and
admissibility remain explicit hypotheses. The proof uses no classification,
character independence, geometric lemma, adjointness or cuspidal-support
theorem. It supplies no central-exponent decomposition, analytic criterion
or proof that reducible rank-one induction forces self-association.

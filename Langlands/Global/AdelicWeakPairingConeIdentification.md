# Identification of the regularized weak constant term pairing

`StandardParabolicFamily.WeakConstantTermRegularizedConeIdentificationStatement`
compares two descriptions of the extended normalized Levi pairing on coroot
slices. The first description is the `UnitaryPairingExpansion` at a standard
parabolic of an `IsWeakConstantTermPairingExpansion`. The second uses a finite
sum of twists of square-integrable inducing forms, a remainder orthogonal on
every positive Levi slice, and an integrable polynomial-exponential
description of the translated pairings of those twists. The inducing forms and
the polynomial exponentials each have their own finite label set. Different
labels may carry the same parameter.

`weakConstantTerm_regularizedConeIntegral_eq` uses `IsWeakConstantTerm.unique`
to identify both weak constant terms. The theorem
`IsSquareIntegrableTwistDecomposition.twistSum_eq` then identifies the sums of
twists in the two decompositions. Pointwise central translation preserves the
equality of these sums. `normalizedPairing_finsetSum` distributes the pairing
over the integrable summands and gives equality of the two pairing evaluations.
Surjectivity in `standardPositiveLog` gives a positive split point for each
coroot coordinate vector. With unitary parameters and nonzero coroot
denominators in both presentations,
`sum_regularizedOrthantTerm_eq_of_eval_eq` gives equality of the regularized
cone integrals at every truncation parameter.

This comparison is derived from the definition of the extended pairing after
(3.7) and the regularization in (7.9)–(7.12) of P. Delorme,
*On the spectral theorem of Langlands*, Advances in Mathematics 426 (2023),
109107, printed pp. 15 and 25. The registered source
`delorme-2023-spectral-theorem-langlands` contains the published PDF.

# Genuine finite tensor presentations after determinant multiplication

This internal construction starts with an existing genuine finite tensor
presentation `P` of a specified finite adelic invariant subspace of actual
automorphic forms. The number field has arbitrary universe, the rank is
any natural number, and the complex local modules have an independent
universe. The character is an actual finite-order Hecke character.

`determinantTwistExceptional` is the union of the original tensor exceptional
set and the proved full integral character-tail bound.
`determinantTwistFactors` uses the existing positive scalar twist by the
actual determinant character at each finite place.
`determinantTwistReference_fixed` proves that the unchanged reference vectors
are fixed outside the enlarged set. Their original nonzeroness is preserved.

The implementation first compares the original tensor space with its
cofinal reindexing at the enlarged exceptional set. It uses the established
restricted tensor map of identity local intertwiners and the linear
equivalence induced by identity component maps; their common underlying
map proves equivariance. `determinantTwistEnlargedEquiv` composes this with
the supplied presentation.

The full-tail character theorem proves that the genuine restricted tensor
action of the local twists equals the global scalar-twisted action.
Pulling this equality across the actual finite-adelic restricted-product
equivalence identifies the finite adelic actions.
`determinantTwistEquiv` then composes the identity comparison, the twist
of the enlarged original presentation, and the established actual
determinant-multiplier equivalence onto its image in automorphic forms.
`determinantTwist` packages the resulting genuine tensor presentation of
that actual multiplied form space.

The application formula identifies this equivalence with actual determinant
multiplication after the enlarged original presentation.
`determinantTwistEnlargedEquiv_pure` proves that a pure tensor from any
admissible enlarged stage maps to the original presentation with exactly
the same entries. The evaluation lemmas consequently multiply the original
adelic function by the value of the positive determinant character,
including the explicit pure-tensor formula.

The provenance is internal composition of the existing restricted tensor
construction, character-tail result, actual finite adelic matrix
equivalence, original supplied presentation, and actual determinant image.
No new occurrence or factorization theorem for arbitrary automorphic
spaces is assumed. This construction supplies no Satake or global
Weil/Galois matching and imposes no irreducibility or nonzeroness condition
on the realized space.

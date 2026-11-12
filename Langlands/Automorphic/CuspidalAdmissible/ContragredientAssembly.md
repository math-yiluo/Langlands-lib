# Contragredient existence from joint admissibility

Module: `Langlands.Automorphic.CuspidalAdmissible.ContragredientAssembly`. Provenance:
internal.

`contragredientExistence_of_isJointlyAdmissible hA`: if every actual unitary cuspidal
realization is jointly admissible, then
`Langlands.Automorphic.CuspidalUnitaryContragredientExistenceStatement.{uF}` holds.

Proof: given `T` with unitary central character, the Library theorem
`CuspidalOperatorRealization.isUnitarizable_of_hasUnitaryCentralCharacter` supplies a unitary
form `b` (the band `L²` form). The candidate contragredient is the pointwise complex conjugate
`T.conjugate` with the antilinear bijection `T.conjugateEquiv`, which commutes with the finite,
compact and real Lie operators (`conjugateEquiv_finite`, `conjugateEquiv_compact`,
`conjugateEquiv_lieAction`). The Library criterion
`OperatorRealization.isContragredientOf_of_unitaryForm b hA` then shows that `T.conjugate`
is contragredient to `T`, and `HasUnitaryCentralCharacter.conjugate` gives the unitary central
character of `T.conjugate`.

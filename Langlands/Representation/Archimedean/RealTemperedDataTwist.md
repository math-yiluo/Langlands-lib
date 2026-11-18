# Transporting tempered form and commutant data through determinant twists

This internal helper transports the two explicit analytical prerequisites in
`RealTemperedCommutantReduction` along the determinant-twist equivalence.
It does not prove that either prerequisite holds.

Given a form `B` on the twisted standard module, `pullbackForm` assigns
`B(E v, E w)` to source vectors, where `E = twistEquiv s ds hr`.
Nontriviality transports by the linear equivalence, and injectivity of `E`
preserves diagonal anisotropy. Compact invariance follows because the
twist intertwines the compact action.

For each real Lie direction, write its scalar shift under `E` as `d`.
If the target form identity has scalar `c`, expanding the two shifted
arguments gives a source identity with scalar `c - d - conj(d)`.
Thus `hasTemperedForm_of_twist` proves that all the sufficient form data,
including their scalar allowance, pull back to the original standard module.

For `hasScalarCommutant_of_twist`, conjugate a source endomorphism `A` by
`E`, obtaining `T = E A E⁻¹`. The compact intertwining identity makes `T`
commute with the target compact action. For every complexified Lie direction
the scalar shift commutes with `A`, so the same expansion proves that `T`
commutes with the target Lie action. If the target simultaneous commutant
is scalar, so is `T`, hence so is `A`.

These are derived algebraic statements about the existing concrete function
model. Together with the zero-real-exponent normalization they allow the
analytical form and commutant proofs to work after removal of a common real
determinant exponent. No Langlands quotient or classification theorem is used.

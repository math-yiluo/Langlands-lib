# Proof of `LeviJacquetContragredientFromInputsStatement`

Authors: Worker 1402 and Worker 937. Lean module
`Langlands.Representation.Exponents.LeviJacquetContragredientFromInputsProof`, namespace
`Langlands.Aubert.General.RepresentedParabolic`.

## Source

Renard 2026, *Représentations des groupes réductifs p-adiques*, VI.9.6, second Theorem
(VI.9.6.2) (printed p.201, PDF p.207). The source ID is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

## Declaration

### `leviJacquetContragredientFromInputs`

`LeviJacquetContragredientFromInputsStatement.{u, v}` holds. If `ParabolicDynamicStatement`,
`OppositeDynamicParabolicUniquenessStatement`,
`UniformCompressionStabilizationStatement.{u, v}` and
`Dynamic.LeviAdjointDeterminantReciprocityStatement` hold, then so does
`LeviJacquetContragredientStatement.{u, v}`.

Proof. Introduce the four premises and apply `leviJacquetContragredient_of_structure`
(`Exponents/LeviJacquetContragredientStructure.lean`), which takes them in the same order.
That theorem uses the proved `dynamicGeometricUnipotentRadical` for the radicals. See
`LeviJacquetContragredientStructure.md` for the reduction to the dynamic case.

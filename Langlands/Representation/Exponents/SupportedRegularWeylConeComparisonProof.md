# Proof of the supported regular Weyl and cone comparison

Authors: Worker 960 and Worker 165.

`Langlands.glSupportedRegularWeylConeComparison.{uF,uV1,uV2,uM1,uM2,uW1,uW2,uJ}`
proves exactly
`Langlands.GLSupportedRegularWeylConeComparisonStatement.{uF,uV1,uV2,uM1,uM2,uW1,uW2,uJ}`.
All eight universes are independent. The theorem has no additional premise.
The target's Lean/Markdown pair and its imported files are unchanged.

The theorem applies the reduction
`Langlands.SupportedRegularWeylCone.reduction` from
[`SupportedRegularWeylConeReduction`](SupportedRegularWeylConeReduction.md).
That reduction proves the target from tempered induction preservation
`Langlands.GLTemperedInductionPreservationStatement`, one instance for each
side. This module supplies both instances with the published theorem
`Langlands.glTemperedInductionPreservation` from
`Langlands.Representation.Classification.TemperedInductionPreservationProof`.
It is used at `.{uF, uW1}` for the first coarse tempered representation and at
`.{uF, uW2}` for the second. Preservation is therefore a proved input, not an
assumption of the final theorem.

The reduction also uses the published theorems
`Langlands.glInducedCuspidalExponentPersistence`,
`Langlands.glTemperedOppositeTwistCone` and
`Langlands.Exponents.supportedRegularWeylParameterNumerics`, together with the
helpers in
[`SupportedRegularWeylParameterHelpers`](SupportedRegularWeylParameterHelpers.md).
It returns one permutation `w` and one fine-Levi conjugacy witness `hw` for
all four clauses of the target: the twisted fine equivalence, the fixed
relation `V1 (w.symm a) - A1 (w.symm a) = V2 a - A2 a`, and both closed
positive-root cone conditions. The reduction's Markdown describes that
argument. It applies one comparison to each side and reconciles the two
permutations with the third clause of the numerics theorem.

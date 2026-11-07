# Proof of `LeviSecondAdjointnessFromInputsStatement`

Authors: Worker 1402 and Worker 937. Lean module
`Langlands.Representation.Exponents.LeviSecondAdjointnessFromInputsProof`, namespace
`Langlands.Aubert.General.RepresentedParabolic`.

## Source

Renard 2026, *Représentations des groupes réductifs p-adiques*, VI.9.6, first Theorem
(VI.9.6.1) (printed p.201, PDF p.207; the proof is on printed pp.201–205, PDF pp.207–211).
The source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

## Declaration

### `leviSecondAdjointnessFromInputs`

`LeviSecondAdjointnessFromInputsStatement.{u, v}` holds. If `ParabolicDynamicStatement`,
`OppositeDynamicParabolicUniquenessStatement`,
`UniformCompressionStabilizationStatement.{u, max u v}`,
`Dynamic.LeviAdjointDeterminantReciprocityStatement`,
`RationalReductiveUnimodularityStatement`, `StandardCocharacterStatement` and
`ArbitraryParabolicQuotientCompactStatement` hold, then so does
`LeviSecondAdjointnessStatement.{u, v}`.

Proof. Introduce the seven premises and apply `leviSecondAdjointness_of_structure`
(`Exponents/LeviSecondAdjointnessStructure.lean`), which takes them in the same order.
That theorem uses the proved `dynamicGeometricUnipotentRadical` for the radicals. See
`LeviSecondAdjointnessStructure.md` for how the general second adjointness theorem is
applied to point images.

# All-field port of `Langlands.Representation.Classification.SegmentConstituentCentralCharacterProof`

`Langlands.AllField.Representation.Classification.SegmentConstituentCentralCharacterProof` is the all-field port of the Library module `Langlands.Representation.Classification.SegmentConstituentCentralCharacterProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Classification.SegmentConstituentCentralCharacterProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**The scalar action on segment inductions and their constituents**

Ambient scalar matrices lie in every standard block Levi as constant block
scalars, the explicit block modulus is trivial on them, and normalized
parabolic induction acts on them through the inducing Levi representation.
The scalar characters of block factors multiply in their tensor product. For
the segment factors `ν^i A` the determinant powers add up to the exponent
`m (m - 1) / 2`, for both orders of the factors. Constituents inherit the
scalar character through their actual injective or surjective intertwiners.

## Imports from the port

- `Langlands.AllField.Group.GL.BlockIwahoriDefinitionsSupplement`
- `Langlands.AllField.Representation.Induction.BlockFactors`

## Declarations

- `Langlands.LocalFieldData.hasScalarCharacter_normalizedParabolicInduced` (theorem): A scalar character of the inducing Levi representation on the constant block
  scalars is the scalar character of its normalized parabolic induction.
- `Langlands.LocalFieldData.hasScalarCharacter_normalizedProductInduced` (theorem): If each block factor `σ i` has scalar character `c i`, then
  `i(σ_1, …, σ_r)` has scalar character `∏ i, c i`.

Public declarations of the original that are not re-declared here: `Langlands.GeneralLinear.BlockShape.scalarLevi`, `Langlands.GeneralLinear.BlockShape.scalarLevi_apply`, `Langlands.GeneralLinear.BlockShape.leviEmbedding_scalarLevi`, `Langlands.GeneralLinear.BlockShape.scalarParabolic`, `Langlands.GeneralLinear.BlockShape.coe_scalarParabolic`, `Langlands.GeneralLinear.BlockShape.leviProjection_scalarParabolic`, `Langlands.GeneralLinear.BlockShape.hasScalarCharacter_blockTensor`, `Langlands.Classification.hasScalarCharacter_twist`, `Langlands.Classification.sum_fin_val_real`, `Langlands.Classification.sum_fin_rev_val_real`, `Langlands.PadicField.TopologicalData.leviHalfModulus_scalarLevi`, `Langlands.PadicField.TopologicalData.parabolicHalfModulus_scalarParabolic`, `Langlands.PadicField.TopologicalData.coe_determinantPowerCharacter_scalar`, `Langlands.PadicField.TopologicalData.prod_twistedScalarCharacter`, `Langlands.PadicField.TopologicalData.hasScalarCharacter_segmentFactor`, `Langlands.PadicField.TopologicalData.hasScalarCharacter_segmentInduced`, `Langlands.PadicField.TopologicalData.hasScalarCharacter_segmentInducedDown`, `Langlands.Classification.segmentConstituentCentralCharacter`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.

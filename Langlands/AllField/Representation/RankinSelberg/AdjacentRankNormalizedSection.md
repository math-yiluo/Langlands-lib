# All-field port of `Langlands.Representation.RankinSelberg.AdjacentRankNormalizedSection`

`Langlands.AllField.Representation.RankinSelberg.AdjacentRankNormalizedSection` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.AdjacentRankNormalizedSection`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field, carrying either bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`) or the corresponding instances (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`. Declarations that take explicit data `T : F.TopologicalData` in the original take explicit data `T : LocalFieldData F` in the port.

Source: the original module `Langlands.Representation.RankinSelberg.AdjacentRankNormalizedSection` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Compact-orbit sections in the exact normalized adjacent-rank lower induction.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.LastRowCompactOrbitProof`
- `Langlands.AllField.Representation.RankinSelberg.RankOneExtensionCharacter`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockJacquetConvergence.RadicalIwasawa`

## Declarations

- `Langlands.AllField.RankinSelberg.adjacentRankDeterminantWeight` (def): The smooth determinant weight `χ(det g) |det g|^s`.
- `Langlands.AllField.RankinSelberg.adjacentRankDeterminantWeight_apply` (theorem).
- `Langlands.AllField.RankinSelberg.adjacentRankDeterminantWeight_locallyConstant` (theorem): The scalar inner weight is locally constant on the actual general linear group.
- `Langlands.AllField.RankinSelberg.adjacentRankLower_determinantComplexPower` (theorem): The actual determinant power splits over the two lower diagonal blocks.
- `Langlands.AllField.RankinSelberg.adjacentRankLowerScalarProjection` (def): The scalar diagonal block, with its rank made explicit.
- `Langlands.AllField.RankinSelberg.adjacentRankLower_halfModulus` (theorem): The opposite half-modulus on the exact ordered lower shape.
- `Langlands.AllField.RankinSelberg.adjacentRankLower_weightRatio` (theorem): The two weights in JPSS (10) give exactly the lower normalized character.
- `Langlands.AllField.RankinSelberg.Padic.adjacentRankLowerTensorCoordinates_action` (theorem): The host's block tensor action in original-module coordinates.
- `Langlands.AllField.RankinSelberg.Padic.adjacentRankLowerCompactRepresentation` (abbrev): The actual parabolic action obtained from the compact average.
- `Langlands.AllField.RankinSelberg.Padic.adjacentRankLowerTensorRepresentation` (abbrev): The exact tensor-valued inducing representation in the host target.
- `Langlands.AllField.RankinSelberg.Padic.adjacentRankLowerInducingCoordinates` (def): Original-module coordinates identify the compact-section action with the
  host's normalized inducing action.
- `Langlands.AllField.RankinSelberg.Padic.adjacentRankNormalizedSection` (def): The compact full-rank section in the exact canonical normalized lower induction.
- `Langlands.AllField.RankinSelberg.Padic.adjacentRankNormalizedSection_eval` (theorem): Evaluation retains the literal compact-average formula on the original module.
- `Langlands.AllField.RankinSelberg.Padic.adjacentRankNormalizedSectionTensor` (def): The normalized section map on the full compact-test/original-vector tensor product.
- `Langlands.AllField.RankinSelberg.Padic.adjacentRankNormalizedSectionTensor_tmul` (theorem).
- `Langlands.AllField.RankinSelberg.Padic.adjacentRankNormalizedSection_right` (theorem): The exact induced action has the weighted test-translation formula.

Public declarations of the original that are not re-declared here: `Langlands.Shahidi.complexPower_comp`, `Langlands.RankinSelberg.adjacentRankLowerTensorCoordinates`, `Langlands.RankinSelberg.adjacentRankLowerTensorCoordinates_pairTensor`, `Langlands.RankinSelberg.adjacentRankLowerTensorCoordinates_symm`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.

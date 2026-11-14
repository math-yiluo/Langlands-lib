# All-field port of `Langlands.Representation.RankinSelberg.EqualRankTrilinearMirabolicPrerequisites`

`Langlands.AllField.Representation.RankinSelberg.EqualRankTrilinearMirabolicPrerequisites` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.EqualRankTrilinearMirabolicPrerequisites`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.EqualRankTrilinearMirabolicPrerequisites` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Equal-rank assembly with the GL finite-length inputs discharged.

## Imports from the port

- `Langlands.AllField.Group.GL.CompactOpenSupplement`
- `Langlands.AllField.Group.GL.UnramifiedCharacterSupplement`
- `Langlands.AllField.Representation.Classification.FiniteLengthProof`
- `Langlands.AllField.Representation.CuspidalSupport.CuspidalTensorStatement`
- `Langlands.AllField.Representation.CuspidalSupport.JacquetDetectingFamilyLengthProof`
- `Langlands.AllField.Representation.CuspidalSupport.JacquetInductionStatement`
- `Langlands.AllField.Representation.CuspidalSupport.JacquetSubquotientProof`
- `Langlands.AllField.Representation.CuspidalSupport.NormalizedCuspidalInductionStatementSupplement`
- `Langlands.AllField.Representation.CuspidalSupport.TotalConjugatingCountStatement`
- `Langlands.AllField.Representation.Geometric.GeometricLemmaStatement`
- `Langlands.AllField.Representation.Induction.SingleBlockSupplement`
- `Langlands.AllField.Representation.Parabolic.RefinementCompositionSupplement`
- `Langlands.AllField.Representation.RankinSelberg.EqualRankTrilinearPrerequisites`

## Declarations

- `Langlands.AllField.RankinSelberg.EqualRankTrilinearMirabolicPrerequisites` (def): The seven remaining inputs after applying the published GL finite-length proof.
- `Langlands.AllField.RankinSelberg.equalRankTrilinearPrerequisites_of_mirabolic` (theorem): The GL finite-length theorem supplies the two omitted premises.
- `Langlands.AllField.RankinSelberg.equalRankTrilinearUniqueness_of_mirabolic_prerequisites` (theorem): Equal-rank uniqueness from the remaining mirabolic and Frobenius inputs.

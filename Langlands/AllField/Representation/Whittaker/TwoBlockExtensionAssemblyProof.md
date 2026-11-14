# All-field port of `Langlands.Representation.Whittaker.TwoBlockExtensionAssemblyProof`

`Langlands.AllField.Representation.Whittaker.TwoBlockExtensionAssemblyProof` is the all-field port of the Library module `Langlands.Representation.Whittaker.TwoBlockExtensionAssemblyProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field, carrying either bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`) or the corresponding instances (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`. Declarations that take explicit data `T : F.TopologicalData` in the original take explicit data `T : LocalFieldData F` in the port.

Source: the original module `Langlands.Representation.Whittaker.TwoBlockExtensionAssemblyProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Conditional proof of the JPSS two-block extension**

## Imports from the port

- `Langlands.AllField.HarmonicAnalysis.MatrixFourierSliceProof`
- `Langlands.AllField.Representation.Induction.BlockEquivalence`
- `Langlands.AllField.Representation.Whittaker.TwoBlockCellCoefficientProof`
- `Langlands.AllField.Representation.Whittaker.TwoBlockExtensionAssemblyStatement`

## Declarations

- `Langlands.AllField.Whittaker.twoBlockHalfModulus_mul_detPow` (theorem): The positive induction half and the rectangular Jacobian give the positive
  half power in the JPSS leading-block formula.
- `Langlands.AllField.Whittaker.twoBlockWhittakerExtension_of_rowFourierSurjectivity` (theorem): The full unchanged extension target follows once row Fourier surjectivity
  is available for the canonical topology in every dimension.

Public declarations of the original that are not re-declared here: `Langlands.Whittaker.twoBlockLeadingEmbedding_eq`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.

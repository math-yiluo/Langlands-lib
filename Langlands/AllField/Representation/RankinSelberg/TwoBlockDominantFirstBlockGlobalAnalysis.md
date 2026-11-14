# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockDominantFirstBlockGlobalAnalysis`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantFirstBlockGlobalAnalysis` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockDominantFirstBlockGlobalAnalysis`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockDominantFirstBlockGlobalAnalysis` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Global convergence for the upper first-block disintegration**

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantFirstBlockRowAnalysis`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFirstBlockRadicalAnalysis`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock.firstBlockUpperGlobalAverage` (def): The upper first-block coefficient integrated over the remaining external
  second-block columns, with the actual supplied quotient and rectangle measures.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock.firstBlockUpperRowAverage_joint_stronglyMeasurable` (theorem): Joint measurability retains the radical, small quotient and remaining
  external columns. No measurable quotient representative is chosen.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock.firstBlockUpperRowAverage_joint_product_control` (theorem): The original raw norm on the actual radical/quotient product controls the
  three-variable row average and justifies moving the remaining columns outside.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock.integrable_firstBlock_radical_product_ae` (theorem): Composing the exact first-block and radical towers gives genuine
  integrability on the actual radical/small-quotient product almost everywhere
  on the lower mixed zero slice. This applies to any measurable raw profile.

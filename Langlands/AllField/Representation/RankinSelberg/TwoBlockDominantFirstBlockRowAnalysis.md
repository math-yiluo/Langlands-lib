# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockDominantFirstBlockRowAnalysis`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantFirstBlockRowAnalysis` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockDominantFirstBlockRowAnalysis`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockDominantFirstBlockRowAnalysis` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Measurable row averages and the original raw-norm majorant**

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantFirstBlockRectangleChange`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock.continuous_translated_unequalRankIntegrandAt` (theorem): Joint continuity on the actual quotient, with the rectangular and
  right-translation parameters both retained.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock.firstBlockUpperColumnNormProfile` (def): Integrate the norm after averaging the external first-block rows.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock.firstBlockUpperRowAverage_column_control` (theorem): At each original rectangle fiber, the row average is integrable in the
  remaining columns, its real norm integral is bounded by the original raw norm,
  and its signed integral is the original rectangle average.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.TwoBlockDominantFirstBlock.firstBlockUpperRowAverage_stronglyMeasurable`, `Langlands.RankinSelberg.TwoBlockDominantFirstBlock.firstBlockUpperColumnNormProfile_measurable`, `Langlands.RankinSelberg.TwoBlockDominantFirstBlock.firstBlockUpperRowAverage_product_control`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.

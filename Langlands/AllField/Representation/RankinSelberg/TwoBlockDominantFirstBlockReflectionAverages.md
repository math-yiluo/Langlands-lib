# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockDominantFirstBlockReflectionAverages`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantFirstBlockReflectionAverages` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockDominantFirstBlockReflectionAverages`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockDominantFirstBlockReflectionAverages` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Convergent reflected first-block averages**

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantFirstBlockReflectionCoefficients`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantKernelRegularity`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock.firstBlockReflectedRowAverage` (def): The actual reflected small rectangle average with its spectral factor.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock.firstBlockReflectedColumnNormProfile` (def): The remaining-column norm profile of the actual reflected row average.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock.continuous_firstBlockDualFiberIntegrand_reflection` (theorem): Joint continuity of the reflected integrand descends through the open
  quotient map; its representative formula is the actual lower test matrix.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock.firstBlockReflectedRowAverage_stronglyMeasurable` (theorem): Joint measurability of the actual quotient/column average needs no
  measurable choice of representatives.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock.firstBlockReflectionDensity` (def): The positive real density in the lower first-block slice tower.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock.firstBlockReflectionDensity_nonneg` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock.firstBlockReflectedRowAverage_mk_on_slice` (theorem): The exact coefficient calculation at a representative on the small slice.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock.firstBlockReflectedRowAverage_column_control` (theorem): Genuine lower rectangle convergence controls the remaining columns of
  the actual reflected average, with the integral of the raw norm retained.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock.firstBlockReflectedRowAverage_product_control` (theorem): The actual lower raw norm supplies quotient/column product convergence.
  Fubini then identifies the integrated reflected coefficient with the actual
  unweighted lower first-block average and its positive density.

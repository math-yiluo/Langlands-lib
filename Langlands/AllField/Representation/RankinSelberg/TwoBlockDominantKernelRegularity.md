# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockDominantKernelRegularity`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantKernelRegularity` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockDominantKernelRegularity`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockDominantKernelRegularity` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Regularity of the actual dominant rectangle kernel**

The raw weighted kernel is continuous for smooth coefficient-image tests.
Its total rectangle averages and the set of integrable rectangle fibers are
measurable, both on representatives and on the lower quotient.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.AdjacentRankModelConvergenceProof`
- `Langlands.AllField.Representation.RankinSelberg.QuotientIwasawaIntegrationProof`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantQuotientKernelData`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerIntegrandRegularity`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.continuous_kernel` (theorem): Smoothness alone gives joint continuity of the actual weighted raw kernel,
  with no absolute-integrability premise.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.measurable_representativeKernel` (theorem): The complex total rectangle integral is measurable even when some fibers
  are not integrable.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.measurable_representativeNormProfile` (theorem): Measurability concerns the integral of the raw norm, retaining the exact
  supplied rectangle Haar measure.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.measurable_quotientKernel` (theorem): Measurability of the actual complex average descends without choosing
  representatives.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.measurable_quotientNormProfile` (theorem): The actual real raw-norm profile is measurable on the lower quotient.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.TwoBlockDominantRectangular.continuous_rectangleUnipotent`, `Langlands.RankinSelberg.TwoBlockDominantRectangular.continuous_append`, `Langlands.RankinSelberg.TwoBlockDominantRectangular.continuous_matrix`, `Langlands.RankinSelberg.TwoBlockDominantRectangular.continuousKernel`, `Langlands.RankinSelberg.TwoBlockDominantRectangular.continuousKernel_apply`, `Langlands.RankinSelberg.TwoBlockDominantRectangular.measurableSet_fiberIntegrable`, `Langlands.RankinSelberg.TwoBlockDominantRectangular.measurableSet_quotientFiberIntegrable`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.

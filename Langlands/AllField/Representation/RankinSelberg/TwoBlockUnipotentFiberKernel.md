# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockUnipotentFiberKernel`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockUnipotentFiberKernel` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockUnipotentFiberKernel`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockUnipotentFiberKernel` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**The actual two-block radical fiber kernel**

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.TwoBlockUnipotentQuotientData`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockUnipotentQuotient.map_unipotentShift` (theorem): The affine radical coordinate change induced by an upper unipotent
  matrix preserves the supplied additive Haar measure.
- `Langlands.AllField.RankinSelberg.TwoBlockUnipotentQuotient.measurable_fiberMeasures` (theorem): Joint measurability makes the representative fiber measures measurable
  as a map from the ambient group to the space of measures.
- `Langlands.AllField.RankinSelberg.TwoBlockUnipotentQuotient.fiberMeasures_upperUnipotent_mul` (theorem): The representative fiber measures are invariant under changing the
  representative by left multiplication from the full unipotent subgroup.
- `Langlands.AllField.RankinSelberg.TwoBlockUnipotentQuotient.fiberKernel` (def): The actual descended measure kernel. Its value is the prescribed
  pushforward of the supplied radical measure, without normalization.
- `Langlands.AllField.RankinSelberg.TwoBlockUnipotentQuotient.fiberKernel_mk` (theorem): Representative evaluation of the descended kernel is exact.

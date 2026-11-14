# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockLowerFixedSliceMeasureTransport`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFixedSliceMeasureTransport` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockLowerFixedSliceMeasureTransport`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockLowerFixedSliceMeasureTransport` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Measures and slice transport for the Section 4.7 lower quotient**

The lower measure is exactly the pushforward by the inverse block-rotation
homeomorphism. Compatibility and sigma-finiteness follow from the published
normalized standard quotient construction. Restriction commutes with this
pushforward, which transfers absolute integrability and both integrals.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerUnipotentQuotientData`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockLowerFixedSlice.lowerMeasure` (def): The measure used on the lower quotient, with exactly the prescribed scale.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFixedSlice.lowerMeasure_restrict` (theorem): Restricting the transported measure to a determinant slice is the transport
  of the standard measure restricted to the corresponding standard slice.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFixedSlice.integrable_lowerMeasure_iff` (theorem): Absolute integrability is preserved in both directions by the prescribed
  restricted transport; no convergence assumption is hidden in an integral identity.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFixedSlice.integral_lowerMeasure` (theorem): Restricted complex and real integral transport, valid for every Banach-valued
  function, including the actual integrand and its norm.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFixedSlice.sigmaFinite_lowerMeasure` (theorem): Sigma-finiteness of a standard quotient measure passes to its lower transport.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFixedSlice.compatible_measure_data` (theorem): The exact normalized standard quotient measure exists, and every compatible
  measure and its prescribed lower transport are sigma-finite.

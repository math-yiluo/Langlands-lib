# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockDominantRectangleHaar`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantRectangleHaar` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockDominantRectangleHaar`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockDominantRectangleHaar` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Exact supplied Haar measure on the two dominant rectangles**

The determinant-one laws of the actual multipliers imply preservation of the
supplied product measure. Both rectangle dimensions may be zero.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerUnipotentQuotientData`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.rectangleMeasure` (def): The exact nested product of the supplied scalar additive Haar measure.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.rectangleMeasure_sigmaFinite` (instance).
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.rectangleChangeHomeomorph` (def): The already constructed rectangle equivalence, with its proved topology.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.measurePreserving_rectangleChange` (theorem): The actual simultaneous change preserves the exact product for every supplied
  additive Haar, including either empty rectangle. No Jacobian premise is required.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.integral_rectangleChange` (theorem): Total Bochner change of variables; it does not assert integrability.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.integrable_rectangleChange_iff` (theorem): Actual integrability is equivalent in both directions, for arbitrary inputs.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.TwoBlockDominantRectangular.rectangleMeasure_eq`, `Langlands.RankinSelberg.TwoBlockDominantRectangular.measurePreserving_rectangleChange_symm`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.

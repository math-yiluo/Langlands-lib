# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockDominantRectangleBoxes`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantRectangleBoxes` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockDominantRectangleBoxes`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockDominantRectangleBoxes` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Lattice boxes for the actual dominant rectangles**

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantFirstRectangleSupport`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFixedSliceCoordinates`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.mem_box_iff_normalizedAbs` (theorem): Membership in the standard lattice box is an entrywise absolute-value bound.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.exists_box_of_isCompact` (theorem): Every compact set of rectangular matrices is contained in one standard box.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.box_mul` (theorem): Multiplication adds entrywise denominator exponents, including for nonsquare matrices.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.mem_box_of_mul_mem_box` (theorem): A bounded inverse removes a right matrix factor at the cost of its exponent.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.box_neg_transpose` (theorem): Negation and transpose preserve the denominator exponent.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.box_of_reverse` (theorem): Row and column reversal preserve the denominator exponent.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.box_mono` (theorem): Increasing the denominator exponent enlarges the box.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.isEntryBounded_reflected` (theorem): Reversed inverse transpose preserves the common entry bound.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.IsTorusRectangleBoxSupport` (def): The actual nonzero coefficient restricts both rectangles to a common
  box whose exponent is a fixed constant plus the torus size.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.exists_torus_rectangle_box_support` (theorem): Both actual rectangles have a uniform box bound, before all torus and
  right integral parameters.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.measurableSet_rectangle_box` (theorem): The common box for both actual rectangles is measurable.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.rectangleMeasure_box` (theorem): Exact product volume; its exponent counts every entry of both actual rectangles.

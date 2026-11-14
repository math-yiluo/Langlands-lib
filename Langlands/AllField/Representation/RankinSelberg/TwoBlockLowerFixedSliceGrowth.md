# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockLowerFixedSliceGrowth`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFixedSliceGrowth` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockLowerFixedSliceGrowth`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockLowerFixedSliceGrowth` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Growth bounds for the Section 4.7 lower quotient**

The standard-character test coefficient has a uniform geometric growth base.
Block section bounds follow from finite compact images and the exact opposite twist.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.TwoBlockJacquetConvergenceProof`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockLowerFixedSlice.exists_standard_functional_growth` (theorem): The standard-character counterpart of the inverse-functional growth estimate.
  The base depends on the representation and functional, before the vector.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFixedSlice.exists_coefficient_growth` (theorem): Every actual coefficient-image vector inherits the same growth base.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFixedSlice.isEntryBounded_torus` (theorem): A diagonal uniformizer matrix is entry-bounded by any common bound for
  its positive and negative exponents.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFixedSlice.exists_coefficient_torus_growth` (theorem): Uniform growth of actual test coefficients on diagonal/compact coordinates,
  including any fixed left translate such as the block rotation.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFixedSlice.exists_coefficient_torusSize_growth` (theorem): The same coefficient bound with the canonical integral `l¹` size.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFixedSlice.exists_section_growth` (theorem): Uniform block-section growth, with the inverse upper half modulus and both
  opposite twists displayed exactly. The growth base precedes the twist and section.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.TwoBlockLowerFixedSlice.torusSize`, `Langlands.RankinSelberg.TwoBlockLowerFixedSlice.torusSize_bounds`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.

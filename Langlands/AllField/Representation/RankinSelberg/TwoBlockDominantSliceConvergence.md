# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockDominantSliceConvergence`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantSliceConvergence` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockDominantSliceConvergence`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockDominantSliceConvergence` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Genuine slice convergence of the actual dominant kernel**

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.QuotientTorusEnvelope`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantNormEnvelope`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.exists_standard_torus_representative` (theorem): Every actual standard quotient point has a torus times integral
  representative; this is an existence argument, not a chosen section.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.exists_summable_kernelNorm_majorant` (theorem): One threshold before all complementary dimensions gives a summable
  majorant for the actual integrated raw norm and complex average.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.kernelAbsoluteIntegrable_of_summable_torus_bound` (theorem): A measurable actual kernel and raw-norm profile with one summable torus
  bound give genuine absolute input for the exact supplied quotient measure.
  The fiber assertion is extended to every quotient point by Iwasawa coverage.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.kernelAbsoluteIntegrable_restrict` (theorem): Restricting the supplied standard measure restricts all three actual
  absolute-input conditions to the corresponding lower determinant slice.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.IsUniformSliceConvergence` (def): One bound precedes the twist, every supplied compatible measure, both
  rectangle dimensions and all tests. Convergence on each determinant slice
  holds for every spectral parameter, independently of any epsilon equation.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.exists_uniform_slice_convergence` (theorem): The actual raw-norm envelope and quotient integration prove the uniform
  slice convergence package for full Whittaker-type representations.

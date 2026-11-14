# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockDominantSliceSpectral`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantSliceSpectral` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockDominantSliceSpectral`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockDominantSliceSpectral` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Spectral dependence of the actual dominant quotient kernel on each slice**

The exact supplied lower measure and the integral of the raw kernel's norm
are retained. All integrability assertions below are equivalences.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantQuotientKernelData`
- `Langlands.AllField.Representation.RankinSelberg.UnequalRankBilinearUniquenessStatement`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.kernel_spectral` (theorem): Changing the parameter changes only the actual determinant weight.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.representativeKernel_spectral` (theorem): The complex rectangle integral keeps its spectral weight outside.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.representativeNormProfile_spectral` (theorem): The real profile is the integral of the raw norm, with its own weight.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.fiberIntegrable_spectral_iff` (theorem): Fiber integrability is unchanged by the nonzero spectral weight.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.quotientKernel_spectral` (theorem): Actual spectral dependence after descent, without a representative choice.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.quotientNormProfile_spectral` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.quotientFiberIntegrable_spectral_iff` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.kernelSliceCoefficient` (def): The actual zero-parameter coefficient on a lower determinant slice,
  with exactly the transported supplied standard quotient measure.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.quotientKernel_spectral_onSlice` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.quotientNormProfile_spectral_onSlice` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.setIntegral_quotientKernel_spectral` (theorem): The total complex slice integral has the exact coefficient scaling.
  This identity does not assert convergence.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.integrableOn_quotientKernel_spectral_iff` (theorem): Genuine outer integrability on a single slice is equivalent at `s` and zero.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.integrableOn_quotientNormProfile_spectral_iff` (theorem): Genuine outer integrability of the raw-norm profile has the same equivalence.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.ae_quotientFiberIntegrable_spectral_iff` (theorem): The actual fiber condition is equivalent almost everywhere for the exact
  restricted lower measure, independently of outer integrability.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.kernelAbsoluteIntegrable_restrict_spectral_iff` (theorem): Package the three genuine convergence equivalences on one slice using
  the existing absolute-input predicate and restriction of the supplied measure.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.TwoBlockDominantRectangular.kernelNormProfileSliceCoefficient`, `Langlands.RankinSelberg.TwoBlockDominantRectangular.setIntegral_quotientNormProfile_spectral`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.

# All-field port of `Langlands.HarmonicAnalysis.RectangularFourierUnimodularTranslate`

`Langlands.AllField.HarmonicAnalysis.RectangularFourierUnimodularTranslate` is the all-field port of the Library module `Langlands.HarmonicAnalysis.RectangularFourierUnimodularTranslate`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.HarmonicAnalysis.RectangularFourierUnimodularTranslate` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Rectangular Fourier integrals of two-sided unimodular translates**

Two-sided multiplication by invertible matrices of normalized determinant one
preserves the rectangular product measure, and the raw plus-sign rectangular
Fourier integral of `x ↦ f (A * x * B)` at `y` is the Fourier integral of `f`
at `Aᵀ⁻¹ * y * Bᵀ⁻¹`. Elements of a compact subgroup of `GL_n` have normalized
determinant one.

## Imports from the port

- `Langlands.AllField.Group.GL.NormalizedCharacterSupplement`
- `Langlands.AllField.HarmonicAnalysis.PadicRectangularHaarScalingProof`

## Declarations

- `Langlands.AllField.HarmonicAnalysis.measurePreserving_rectangular_mul_mul` (theorem): Two-sided multiplication by matrices of normalized determinant one preserves
  the rectangular product measure.
- `Langlands.AllField.HarmonicAnalysis.rectangularPairing_mul_mul` (theorem): The rectangular pairing is invariant under `x ↦ A x B`, `y ↦ Aᵀ⁻¹ y Bᵀ⁻¹`.
- `Langlands.AllField.HarmonicAnalysis.rectangularFourierIntegral_comp_mul_mul` (theorem): The raw rectangular Fourier integral of a two-sided unimodular translate.
- `Langlands.AllField.HarmonicAnalysis.rectangularFourierIntegral_translate_decomposition` (theorem): A finite decomposition of a two-sided unimodular translate of a Schwartz
  function transfers, with the same coefficients, to the Fourier integrals.

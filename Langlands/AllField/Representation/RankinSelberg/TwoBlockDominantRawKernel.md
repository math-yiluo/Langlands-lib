# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockDominantRawKernel`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantRawKernel` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockDominantRawKernel`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockDominantRawKernel` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Raw scalar data for JPSS Section 4.10**

The coefficient and determinant weight are evaluated on actual representatives.
The final rectangle covariance is specialized to the constructed matrix and residual
unipotent from `TwoBlockDominantCovarianceData`.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFirstBlockQuotientData`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerUnfoldingIntegrandData`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.rawScalarValue` (def): The actual scalar section and test coefficient, before choosing the large-group
  matrix argument.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.determinantWeight_lowerBlockUnipotent_mul` (theorem): The determinant weight on a lower-unipotent translate is unchanged for any complex
  exponent. This uses the determinant-one law of the actual lower subgroup.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.rawKernel` (def): The unweighted scalar kernel at the actual Section 4.10 matrix.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.kernel` (def): The representative-level kernel of Section 4.10(2), with its actual determinant
  weight and with all inverse block Whittaker functionals, including zero.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.kernel_eq` (theorem): Evaluation of the kernel on the actual section, coefficient and matrix.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.rawKernel_covariance` (theorem): The actual unweighted kernel is covariant under the simultaneous rectangle
  change computed from the lower-group element.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.kernel_covariance` (theorem): The weighted representative kernel has the same actual rectangle covariance
  for every complex parameter, using determinant one of the lower-group element.

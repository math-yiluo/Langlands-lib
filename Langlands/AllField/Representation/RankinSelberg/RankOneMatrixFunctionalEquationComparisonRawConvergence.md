# All-field port of `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonRawConvergence`

`Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonRawConvergence` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonRawConvergence`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonRawConvergence` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Raw coefficient-model matrix convergence from the supplied matrix bounds.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.IntegralDeterminant`
- `Langlands.AllField.Representation.RankinSelberg.IwasawaHaarIntegration`
- `Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonMatrixBoxDiagonalBound`
- `Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonTorusEnvelope`
- `Langlands.AllField.Representation.RankinSelberg.UnipotentDiagonalVolume`

## Declarations

- `Langlands.AllField.RankinSelberg.matrixUnipotentNormSlice` (def): The genuine unipotent norm slice of a full-matrix test.
- `Langlands.AllField.RankinSelberg.exists_uniform_matrixUnipotentNormSlice_bound` (theorem): One slice bound works uniformly for every integral right factor.
  The bounded diagonal cutoff is pointwise and precedes integration.
- `Langlands.AllField.RankinSelberg.diagonalBorelDensity` (def): The exact inverse upper-Borel density in diagonal coordinates.
- `Langlands.AllField.RankinSelberg.lintegral_iwasawa_diagonalBorelDensity` (theorem): Iwasawa integration with the unchanged normalized group and torus Haar
  measures, expressed in the density used by the diagonal bound.
- `Langlands.AllField.RankinSelberg.measurable_boundedDiagonalNormIntegrand` (theorem): Measurability of a bounded diagonal geometric norm integrand.
- `Langlands.AllField.RankinSelberg.lintegral_norm_matrixIntegrand_iwasawa` (theorem): Left standard equivariance removes the unipotent character from the
  actual norm slice, while the integral right factor has determinant norm one.
- `Langlands.AllField.RankinSelberg.matrixConvergesOnRight_of_torusEnvelope` (theorem): A finite actual coefficient envelope, together with the supplied matrix
  half-plane, gives genuine raw matrix convergence.
- `Langlands.AllField.RankinSelberg.whittakerCoefficient_matrixConvergesOnRight_of_matrix` (theorem): Smoothness supplies the finite envelope for each actual Whittaker
  coefficient, so the supplied matrix bounds imply its genuine raw convergence.
- `Langlands.AllField.RankinSelberg.matrixConvergesOnRight_inverseTransposePullback` (theorem): The actual transformed matrix half-plane is the ordinary one on the
  inverse-transpose pullback representation.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.glModel_matrixConvergesOnRight_of_matrix`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.

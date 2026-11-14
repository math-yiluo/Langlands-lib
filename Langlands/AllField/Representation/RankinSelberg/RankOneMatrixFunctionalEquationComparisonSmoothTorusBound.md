# All-field port of `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonSmoothTorusBound`

`Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonSmoothTorusBound` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonSmoothTorusBound`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonSmoothTorusBound` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Discrete torus bounds for the actual smooth matrix coefficient family.

## Imports from the port

- `Langlands.AllField.Group.GL.NormalizedCharacterSupplement`
- `Langlands.AllField.Group.GL.PadicBlocksSupplement`
- `Langlands.AllField.Representation.GodementJacquet.AnalyticData`
- `Langlands.AllField.Representation.RankinSelberg.IwasawaTorusPartitionProof`

## Declarations

- `Langlands.AllField.RankinSelberg.matrixIntegrand_exists_principalFixed` (theorem): The entire matrix integrand has a principal right stabilizer independent
  of the spectral exponent.
- `Langlands.AllField.RankinSelberg.measurable_biSmooth_matrixIntegrand` (theorem): Measurability of the genuine integrand, including its complex spectral
  weight, for every member of the actual bi-smooth coefficient span.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.biSmoothMatrixCoefficient_continuous_rightFixed`, `Langlands.RankinSelberg.matrixUniformizerTorusIntegrand`, `Langlands.RankinSelberg.tsum_enorm_biSmooth_matrixIntegrand_lt_top`, `Langlands.RankinSelberg.biSmooth_matrixTorus_convergesOnRight`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.

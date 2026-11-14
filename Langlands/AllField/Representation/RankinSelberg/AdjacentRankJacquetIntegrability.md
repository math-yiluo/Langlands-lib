# All-field port of `Langlands.Representation.RankinSelberg.AdjacentRankJacquetIntegrability`

`Langlands.AllField.Representation.RankinSelberg.AdjacentRankJacquetIntegrability` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.AdjacentRankJacquetIntegrability`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.AdjacentRankJacquetIntegrability` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

All-section convergence and coefficient containment for the actual induction.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.AdjacentRankJacquetLinear`
- `Langlands.AllField.Representation.RankinSelberg.AdjacentRankModelMap`
- `Langlands.AllField.Representation.RankinSelberg.AdjacentRankSectionSurjectivity`

## Declarations

- `Langlands.AllField.RankinSelberg.AdjacentJacquet.integrable_realTwist` (theorem): The same representation-uniform real-twist threshold makes the literal
  Jacquet kernel integrable for every actual induced section and every translate.
- `Langlands.AllField.RankinSelberg.AdjacentJacquet.realTwistIntegralLinear` (def): The literal integral at any ambient element, with convergence discharged
  on the exact original-carrier normalized opposite induction.
- `Langlands.AllField.RankinSelberg.AdjacentJacquet.realTwistIntegralLinear_apply` (theorem).
- `Langlands.AllField.RankinSelberg.AdjacentJacquet.realTwistIntegralLinear_coefficient` (theorem): Every coefficient of the identity integral is the literal integral at g.
- `Langlands.AllField.RankinSelberg.AdjacentJacquet.compactTestModelTensor` (def): The compact-test tensor maps into the whole model test space by the
  specified partial Fourier transform and the original coefficient quotient.
- `Langlands.AllField.RankinSelberg.AdjacentJacquet.compactTestModelTensor_tmul` (theorem).
- `Langlands.AllField.RankinSelberg.AdjacentJacquet.integral_normalizedSectionTensor_eq_modelIntegral` (theorem): Exact comparison on the entire compact-test/original-vector tensor product.
- `Langlands.AllField.RankinSelberg.AdjacentJacquet.range_realTwistIntegralLinear_coefficients_subset` (theorem): Every coefficient of the common integral belongs to the whole model image.
  The reverse inclusion, for all Schwartz tests, is a separate obligation.

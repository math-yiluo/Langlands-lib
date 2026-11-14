# All-field port of `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonModelDataConvergence`

`Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonModelDataConvergence` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonModelDataConvergence`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonModelDataConvergence` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Raw original and inverse-transpose bounds from matrix data on the actual model.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonRawConvergence`
- `Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonWeylTransport`

## Declarations

- `Langlands.AllField.RankinSelberg.RawModelIotaMatrixConvergence` (def): The corresponding genuine raw inverse-transpose matrix bound.
- `Langlands.AllField.RankinSelberg.coefficientModelEvaluation_coefficient` (theorem): Evaluation on the actual image realizes its original model function
  as an actual coefficient, with no equivalence from the original carrier.
- `Langlands.AllField.RankinSelberg.whittakerCoefficientIota_matrixConvergesOnRight_of_iota` (theorem): Raw inverse-transpose convergence for a coefficient of an abstract
  smooth representation, before specializing to a coefficient-model carrier.
- `Langlands.AllField.RankinSelberg.rawModelIotaMatrixConvergence_of_modelIota` (theorem): Transformed matrix bounds on the actual model give raw convergence of
  its original inverse-transpose function for every full-matrix test.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.RawModelMatrixConvergence`, `Langlands.RankinSelberg.rawModelMatrixConvergence_of_modelMatrix`, `Langlands.RankinSelberg.rawModel_pair_convergence_of_data`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.

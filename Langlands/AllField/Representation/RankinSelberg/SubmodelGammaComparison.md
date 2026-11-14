# All-field port of `Langlands.Representation.RankinSelberg.SubmodelGammaComparison`

`Langlands.AllField.Representation.RankinSelberg.SubmodelGammaComparison` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.SubmodelGammaComparison`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.SubmodelGammaComparison` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Gamma comparison for an actual subrepresentation of a coefficient model**

The original representation can be reducible. An ambient matrix functional
equation supplies the specified gamma expression on a subrepresentation of its
coefficient model. Existence of a gamma certificate on the original remains a
separate premise.

## Imports from the port

- `Langlands.AllField.Representation.GodementJacquet.SubquotientCoefficientInclusionProof`
- `Langlands.AllField.Representation.RankinSelberg.RankOneAmbientMatrixFunctionalEquationComparisonProof`
- `Langlands.AllField.Representation.Whittaker.ModelGenericSocleProof`

## Declarations

- `Langlands.AllField.RankinSelberg.gamma_eq_submodel` (theorem): A nonzero subrepresentation of the actual coefficient model has the same
  gamma expression against the trivial rank-one test whenever both complete
  certificates already exist. No irreducibility is required.
- `Langlands.AllField.RankinSelberg.gamma_of_submodel_ambient_matrix` (theorem): The actual subquotient map into a submodel supplies the coefficient
  inclusion needed by the ambient matrix comparison. The resulting expression
  is the original representation's gamma factor, provided a complete gamma
  certificate on the original exists. Normalized matrix generators stay on the
  ambient representation.

Public declarations of the original that are not re-declared here: `Langlands.Whittaker.submodelFunctionMap`, `Langlands.Whittaker.submodelEvaluation`, `Langlands.Whittaker.submodelFunctionMap_injective`, `Langlands.Whittaker.coefficientMap_submodelEvaluation`, `Langlands.Whittaker.coefficientModel_submodelEvaluation_le`, `Langlands.Whittaker.submodelEvaluation_ne_zero`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.

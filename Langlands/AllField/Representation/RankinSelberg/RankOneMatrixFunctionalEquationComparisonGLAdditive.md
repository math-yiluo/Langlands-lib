# All-field port of `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonGLAdditive`

`Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonGLAdditive` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonGLAdditive`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonGLAdditive` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Cancelling determinant density for the actual GL Haar measure**

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonFramedIntegrability`
- `Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonGLDensity`

## Declarations

- `Langlands.AllField.RankinSelberg.GLDeterminantDensity.rectangularHaarScalar` (def): One fixed positive normalization scalar for the supplied scalar Haar
  measure, used for every function and test.
- `Langlands.AllField.RankinSelberg.GLDeterminantDensity.rectangularHaarScalar_pos` (theorem).
- `Langlands.AllField.RankinSelberg.GLDeterminantDensity.weightedRestriction_eq_rectangularHaarScalar` (theorem).
- `Langlands.AllField.RankinSelberg.GLDeterminantDensity.forwardWeight_eq_determinantWeight` (theorem).
- `Langlands.AllField.RankinSelberg.GLDeterminantDensity.integrable_generalLinearHaar_natWeight_iff` (theorem): The actual natural matrix-size determinant power converts GL convergence
  to additive convergence on the invertible locus, with the same supplied ν.
- `Langlands.AllField.RankinSelberg.GLDeterminantDensity.integral_generalLinearHaar_natWeight` (theorem): The natural determinant power cancels the density; the one positive
  normalization scalar is retained explicitly.
- `Langlands.AllField.RankinSelberg.GLDeterminantDensity.integrable_prod_generalLinearHaar_natWeight_iff` (theorem): Product-measure convergence for the canonical GL measure and supplied ν.
- `Langlands.AllField.RankinSelberg.GLDeterminantDensity.integral_prod_generalLinearHaar_natWeight` (theorem): The product integral retains the same positive scalar as the single GL
  integral, independently of the auxiliary measure and the integrand.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.GLDeterminantDensity.forwardWeight`, `Langlands.RankinSelberg.GLDeterminantDensity.matrixWeight_mul_forwardWeight`, `Langlands.RankinSelberg.GLDeterminantDensity.integrable_forwardWeight_iff_of_eq_smul`, `Langlands.RankinSelberg.GLDeterminantDensity.integral_forwardWeight_of_eq_smul`, `Langlands.RankinSelberg.GLDeterminantDensity.integrable_prod_forwardWeight_iff_of_eq_smul`, `Langlands.RankinSelberg.GLDeterminantDensity.integral_prod_forwardWeight_of_eq_smul`, `Langlands.RankinSelberg.GLDeterminantDensity.integrable_unipotent_box_generalLinear_natWeight`, `Langlands.RankinSelberg.GLDeterminantDensity.integral_unipotent_box_generalLinear_natWeight_swap`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.

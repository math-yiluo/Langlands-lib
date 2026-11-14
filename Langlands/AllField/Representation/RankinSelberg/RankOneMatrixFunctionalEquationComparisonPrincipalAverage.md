# All-field port of `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonPrincipalAverage`

`Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonPrincipalAverage` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonPrincipalAverage`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonPrincipalAverage` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Right principal averaging and uniform original-integral extraction**

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonUniformBox`
- `Langlands.AllField.Representation.RankinSelberg.RankOneMatrixUnfolding`

## Declarations

- `Langlands.AllField.RankinSelberg.RankOneBox.principalAverage` (def): The actual normalized right average over the principal subgroup.
- `Langlands.AllField.RankinSelberg.RankOneBox.continuous_principalAverage` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneBox.principalAverage_mul` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneBox.principalAverage_equivariant` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneBox.uniformBox_mul_principalLevel` (theorem): The same fixed box is right invariant on the entire matrix space.
- `Langlands.AllField.RankinSelberg.RankOneBox.principalAverage_box_integral` (theorem): Any convergent original box integral is preserved by principal averaging.
- `Langlands.AllField.RankinSelberg.RankOneBox.principalAverage_extraction` (theorem): One fixed box and right averaging extract every continuous equivariant H.
  Only the original-to-averaged direction of convergence is asserted.
- `Langlands.AllField.RankinSelberg.RankOneBox.principalLevel_mass_pos` (theorem): The principal subgroup has finite, strictly positive Haar mass.
- `Langlands.AllField.RankinSelberg.RankOneBox.principalAveragingMeasure` (def): A positive scalar multiple of normalized Haar on the actual principal
  subgroup. Its total mass is C rather than one.
- `Langlands.AllField.RankinSelberg.RankOneBox.principalAveragingMeasure_finite` (instance).
- `Langlands.AllField.RankinSelberg.RankOneBox.principalAveragingMeasure_ae_mem` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneBox.principalAveragingMeasure_ae_det_norm` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneBox.principalAveragingMeasure_integral` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneBox.principalAveragingMeasure_mass` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneBox.principalAveragingMeasure_fixed` (theorem): A principal fixed original function is multiplied by exactly C.
- `Langlands.AllField.RankinSelberg.RankOneBox.principalMeasure_extraction` (theorem): The fixed box extracts the actual compact principal measure average for
  every continuous left equivariant function with convergent original integrand.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.normalizedRightAverage`, `Langlands.RankinSelberg.rightAverage_integral`, `Langlands.RankinSelberg.normalizedRightAverage_integral`, `Langlands.RankinSelberg.normalizedRightAverage_mul_subgroup`, `Langlands.RankinSelberg.normalizedRightAverage_eq_of_fixed`, `Langlands.RankinSelberg.RankOneBox.principalAveragingMeasure_integrable`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.

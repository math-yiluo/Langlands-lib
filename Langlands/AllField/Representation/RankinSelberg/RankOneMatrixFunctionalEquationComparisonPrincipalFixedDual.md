# All-field port of `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonPrincipalFixedDual`

`Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonPrincipalFixedDual` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonPrincipalFixedDual`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonPrincipalFixedDual` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Removing the same principal parameter for a genuinely principal-fixed function.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonPrincipalModelDual`

## Declarations

- `Langlands.AllField.RankinSelberg.principalFixedBlockIntegrand` (def): The unaveraged actual signed complementary block, at the same exponent.
- `Langlands.AllField.RankinSelberg.principalModelBlockIntegrand_ae_of_fixed` (theorem): A principal-fixed function loses no information in the full principal
  parameter: its true weighted integrand is almost everywhere constant in it.
- `Langlands.AllField.RankinSelberg.integrable_principalModelBlockIntegrand_of_fixed` (theorem): Genuine scalar/block convergence implies convergence on the full product
  with the same principal averaging parameter, before taking its average.
- `Langlands.AllField.RankinSelberg.integral_principalModelBlockIntegrand_of_fixed` (theorem): The original principal mass is exactly the scalar relating the fixed
  block integral to the full product integral.
- `Langlands.AllField.RankinSelberg.principalFixedModelDual_pairing` (theorem): For an actual principal-fixed coefficient-model vector, the same original
  box constant multiplies the actual signed block integral. Scalar/block
  convergence supplies the full product bound needed by model approximation.

Public declarations of the original that are not re-declared here: `Langlands.Conductor.inverseTranspose_mem_principalCongruenceSubgroup`, `Langlands.Conductor.inverseTranspose_mem_principalLevelSubgroup`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.

# All-field port of `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonScalarHaar`

`Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonScalarHaar` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonScalarHaar`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Except for the changes described under Proof route below, each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`. Uses of the canonical normed-field structure `F.canonicalNormedField` are replaced by the corresponding facts about `T`.

Source: the original module `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonScalarHaar` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

The exact scalar additive measure and the naturally weighted GL₁ Haar.

## Proof route

Where the original obtains that the punctured neighbourhoods of `0` form a nontrivial filter from the canonical normed-field structure (`NormedField.nhdsNE_neBot` for `F.canonicalNormedField`), the port uses the Library lemma `Langlands.LocalField.nhdsNE_zero_neBot` for the topology of a nonarchimedean local field. Statements are unchanged.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonGLAdditive`

## Declarations

- `Langlands.AllField.RankinSelberg.integrable_generalLinear_one_natWeight_iff` (theorem): The natural determinant exponent one transports genuine scalar convergence
  for every complex function, with the supplied additive Haar normalization.
- `Langlands.AllField.RankinSelberg.integral_generalLinear_one_natWeight` (theorem): The fixed normalization scalar is independent of the scalar integrand.
- `Langlands.AllField.RankinSelberg.integrable_prod_generalLinear_one_natWeight_iff` (theorem): Scalar density cancellation holds on the full product with any auxiliary
  s-finite parameter measure.
- `Langlands.AllField.RankinSelberg.integral_prod_generalLinear_one_natWeight` (theorem): Product integrals have the same normalization scalar as scalar integrals.
- `Langlands.AllField.RankinSelberg.integrable_generalLinear_one_prod_natWeight_iff` (theorem): Full joint convergence with the scalar or GL₁ variable first.
- `Langlands.AllField.RankinSelberg.integral_generalLinear_one_prod_natWeight` (theorem): Scalar-first product integral transport with the identical fixed scalar.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.oneByOneScalarEquiv`, `Langlands.RankinSelberg.oneByOneScalarEquiv_apply`, `Langlands.RankinSelberg.oneByOneScalarEquiv_measurePreserving`, `Langlands.RankinSelberg.rectangularMeasure_one_restrict_invertible`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.

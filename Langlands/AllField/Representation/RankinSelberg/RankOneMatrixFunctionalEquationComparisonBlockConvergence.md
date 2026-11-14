# All-field port of `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonBlockConvergence`

`Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonBlockConvergence` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonBlockConvergence`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonBlockConvergence` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Absolute convergence of the actual rank-one-pair block integrals**

A finite pointwise Schwartz expansion, with model vectors in the original
coefficient image, turns every block integrand into a finite sum of products
of zero-row integrands and compactly supported rectangular tests.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonBoxConvergence`
- `Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonPositiveAssembly`

## Declarations

- `Langlands.AllField.RankinSelberg.RankOneBlockConvergence.integrable_quotient_prod_iff` (theorem): The actual rank-one quotient homeomorphism also transports a product
  with any supplied s-finite rectangular measure.
- `Langlands.AllField.RankinSelberg.RankOneBlockConvergence.converges_of_finite_expansion` (theorem): A finite pointwise Schwartz expansion and convergence of every diagonal
  model restriction imply absolute product convergence of the actual block.
- `Langlands.AllField.RankinSelberg.RankOneBlockConvergence.converges_of_diagonal_integrable` (theorem): Full Whittaker type gives the exact finite expansion used above.
- `Langlands.AllField.RankinSelberg.RankOneBlockConvergence.AllBlocksConvergeOnRight` (def): Absolute convergence of every allowed block with the canonical second
  vector and a specified quotient measure, each on a right half-plane.
- `Langlands.AllField.RankinSelberg.RankOneBlockConvergence.convergesOnRight_of_matrix` (theorem): The supplied matrix convergence gives absolute convergence on a right
  half-plane for every actual block and canonical-vector pair.
- `Langlands.AllField.RankinSelberg.RankOneBlockConvergence.allBlocksConvergeOnRight_of_matrix` (theorem): The actual matrix convergence supplies absolute convergence of all blocks
  for every compatible rank-one quotient measure.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.RankOneBlockConvergence.dualBlockZero_convergesOnRight_of_iota`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.

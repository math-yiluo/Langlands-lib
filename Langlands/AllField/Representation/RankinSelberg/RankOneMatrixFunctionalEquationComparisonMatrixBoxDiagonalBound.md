# All-field port of `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonMatrixBoxDiagonalBound`

`Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonMatrixBoxDiagonalBound` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonMatrixBoxDiagonalBound`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonMatrixBoxDiagonalBound` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Weighted diagonal bounds from genuine full-matrix box integrals.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonSmoothDiagonalBound`
- `Langlands.AllField.Representation.Whittaker.JPSDilationAssemblyProof`

## Declarations

- `Langlands.AllField.RankinSelberg.matrixNormBox` (def): A compact open box in the full square-matrix space, including singular
  matrices, defined using the canonical normalized absolute value.
- `Langlands.AllField.RankinSelberg.isClopen_matrixNormBox` (theorem).
- `Langlands.AllField.RankinSelberg.isCompact_matrixNormBox` (theorem).
- `Langlands.AllField.RankinSelberg.matrixNormBoxTest` (def): The characteristic Schwartz test of the actual full-matrix norm box.
- `Langlands.AllField.RankinSelberg.matrixNormBoxTest_diagonal_of_le` (theorem).
- `Langlands.AllField.RankinSelberg.diagonalSliceWeight` (def): The positive rational weight supplied by the inverse upper-Borel
  modulus and a slice-volume monomial.
- `Langlands.AllField.RankinSelberg.diagonalSliceWeight_nonneg` (theorem).
- `Langlands.AllField.RankinSelberg.boundedDiagonalNormIntegrand` (def): The actual norm integrand with the geometric weight, cut off only by
  a bounded diagonal box.
- `Langlands.AllField.RankinSelberg.enorm_weightedCoefficient_sub_natCast` (theorem): The unchanged determinant weight splits off every nonnegative integral
  power when its spectral exponent is lowered by that integer.
- `Langlands.AllField.RankinSelberg.boundedDiagonalNormIntegrand_le_matrixDiagonal` (theorem): A fixed determinant shift reduces the full weighted box integrand to
  one genuine matrix-test diagonal integrand.
- `Langlands.AllField.RankinSelberg.boundedDiagonalNormIntegrand_convergesOnRight` (theorem): Matrix convergence on one common right half-plane implies genuine
  full-torus convergence of every such bounded diagonal geometric weight.

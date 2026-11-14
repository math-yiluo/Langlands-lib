# All-field port of `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonSmoothDiagonalBound`

`Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonSmoothDiagonalBound` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonSmoothDiagonalBound`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonSmoothDiagonalBound` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Genuine diagonal-torus bounds from ambient matrix convergence.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonSmoothTorusBound`

## Declarations

- `Langlands.AllField.RankinSelberg.measure_diagonalUnits_preimage_principalLevel_le_one` (theorem): The inverse image of an actual principal subgroup under the full diagonal
  homomorphism has finite product multiplicative Haar measure.
- `Langlands.AllField.RankinSelberg.integrable_diagonalUnits_of_principalFixed` (theorem): The actual full diagonal-torus integral inherits ambient integrability
  for every measurable right-principal-fixed complex function.
- `Langlands.AllField.RankinSelberg.matrixDiagonalIntegrand` (def): The literal full-matrix integrand restricted to the full diagonal torus.
- `Langlands.AllField.RankinSelberg.integrable_biSmooth_matrixDiagonalIntegrand` (theorem): A genuinely convergent bi-smooth matrix integrand is integrable on the
  full diagonal torus for its actual product multiplicative Haar measure.
- `Langlands.AllField.RankinSelberg.biSmooth_matrixDiagonal_convergesOnRight` (theorem): The same common shifted matrix half-plane works for all the actual
  full diagonal restrictions, without any uniformizer choice.

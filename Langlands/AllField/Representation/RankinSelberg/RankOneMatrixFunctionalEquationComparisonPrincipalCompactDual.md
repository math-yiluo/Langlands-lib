# All-field port of `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonPrincipalCompactDual`

`Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonPrincipalCompactDual` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonPrincipalCompactDual`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonPrincipalCompactDual` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Compact principal extraction of the actual signed complementary block.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonCompactGLParameters`
- `Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonPrincipalWeighted`
- `Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonSignedCompactPairing`

## Declarations

- `Langlands.AllField.RankinSelberg.principalCompactKernel` (def): The compact principal subgroup indicator is retained until convergence
  has been proved on the full product.
- `Langlands.AllField.RankinSelberg.principalCompactKernel_of_mem` (theorem).
- `Langlands.AllField.RankinSelberg.principalCompactKernel_ae` (theorem).
- `Langlands.AllField.RankinSelberg.principalCompactKernel_detNorm` (theorem).
- `Langlands.AllField.RankinSelberg.principalSignedBlockPoint` (def): The literal complementary-block evaluation point, with its actual signed
  block Weyl factor and inverse transpose of the averaging parameter.
- `Langlands.AllField.RankinSelberg.principalCompactDualIntegrand` (def): The actual principal compact dual block restriction, before averaging.
- `Langlands.AllField.RankinSelberg.glOneWeight_eq_determinantWeight` (theorem): The real GL1 density is the corresponding complex determinant power.
- `Langlands.AllField.RankinSelberg.glOneWeight_smul_natSucc` (theorem): Natural ambient weight and the GL1 density leave exponent one.
- `Langlands.AllField.RankinSelberg.determinantWeight_principalSignedBlockPoint` (theorem): The block restriction preserves the scalar determinant norm when the
  principal averaging parameter has norm one.
- `Langlands.AllField.RankinSelberg.principalCompactDualIntegrand_reconstruct` (theorem): Reconstruction is pointwise; its full-product use below is justified by
  the previously proved parameter convergence.
- `Langlands.AllField.RankinSelberg.principalCompactFourier_reconstruct` (theorem): The natural scalar Fourier orbit has exactly the density used by the
  joint Fourier/block identity.
- `Langlands.AllField.RankinSelberg.parameter_glOneMeasure_density` (theorem): Retaining a parameter commutes with passing to the actual weighted
  GL1 measure.
- `Langlands.AllField.RankinSelberg.parameter_glOneMeasure_block_density` (theorem): Both the compact parameter and the complementary block commute with
  the true weighted GL1 measure, before any averaging.
- `Langlands.AllField.RankinSelberg.principalCompactDual_fourierOrbit_duality` (theorem): The compact principal parameter remains in the full complementary-block
  integral: no cancellation inside its average is used for convergence.
- `Langlands.AllField.RankinSelberg.tsupport_boxLatticeTest_subset` (theorem): The fixed lattice test is supported in its actual compact open box.
- `Langlands.AllField.RankinSelberg.principalCompactDual_pairing` (theorem): One original box test and its same principal measure give the actual
  signed complementary block identity for every compact Whittaker input, with
  both full product convergence and no additional scalar.
- `Langlands.AllField.RankinSelberg.principalCompactDual_pairing_weighted` (theorem): Determinant twisting takes place on the actual compact group function.
  The same original box and same principal measure work for every complex
  spectral exponent, with genuine full product convergence.

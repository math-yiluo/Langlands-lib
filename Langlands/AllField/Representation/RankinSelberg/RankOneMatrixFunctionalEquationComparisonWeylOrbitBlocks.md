# All-field port of `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonWeylOrbitBlocks`

`Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonWeylOrbitBlocks` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonWeylOrbitBlocks`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonWeylOrbitBlocks` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

The scalar Fourier orbit and complementary block orbit for the same matrix test.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonFourierInvariance`
- `Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonWeylBlockFourier`

## Declarations

- `Langlands.AllField.RankinSelberg.determinantNorm_rankOneSignedBlockWeyl` (theorem): The signed complementary Weyl matrix has normalized determinant norm one.
- `Langlands.AllField.RankinSelberg.signedWeylOrbit_blockOrbit_fourier_duality` (theorem): For the same test and norm-one h, the true scalar Fourier orbit and
  complementary block orbit are jointly integrable and have equal integrals.
  The scalar sign substitution preserves the supplied additive Haar exactly.
- `Langlands.AllField.RankinSelberg.signedWeylOrbit_blockOrbit_fourier_duality_averaged` (theorem): Fubini puts the scalar outside the actual Fourier orbit and the
  scalar/block pair outside the original orbit, with genuine convergence.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.inverseTranspose_rankOneWeylLeadingSign`, `Langlands.RankinSelberg.inverseTranspose_rankOneSignedBlockWeyl`, `Langlands.RankinSelberg.signedWeylOrbitFourierKernel`, `Langlands.RankinSelberg.signedBlockOrbitKernel`, `Langlands.RankinSelberg.signedBlockOrbitKernel_at_generalLinear`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.

# All-field port of `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonBoxFourier`

`Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonBoxFourier` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonBoxFourier`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonBoxFourier` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

The actual Fourier transform of the rank-one comparison box.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonLatticeFourier`
- `Langlands.AllField.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonBox`

## Declarations

- `Langlands.AllField.RankinSelberg.RankOneBox.levelSet_eq_additiveLattice` (theorem): The actual maximal-ideal power used by the published box is precisely the
  negative-index valuation lattice.
- `Langlands.AllField.RankinSelberg.RankOneBox.boxLatticeCentre` (def): The comparison box has centre zero in its first row and the identity in
  all remaining rows.
- `Langlands.AllField.RankinSelberg.RankOneBox.box_eq_rectangularLatticeCoset` (theorem): Identification of the actual published box as an entrywise affine lattice
  coset; this is an equality of subsets of the full matrix space.
- `Langlands.AllField.RankinSelberg.RankOneBox.boxLatticeTest` (def): The original comparison box test, expressed through its actual lattice
  coset rather than through an unspecified Fourier partner.
- `Langlands.AllField.RankinSelberg.RankOneBox.boxLatticeTest_apply` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneBox.boxLatticeTest_eq_compactOpenIndicator` (theorem): This is exactly the compact-open indicator in the existing box-integral
  proof, as a Schwartz test on all matrices.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.RankOneBox.boxLatticeLevels`, `Langlands.RankinSelberg.RankOneBox.rectangularPairing_boxLatticeCentre`, `Langlands.RankinSelberg.RankOneBox.boxFourierSupport`, `Langlands.RankinSelberg.RankOneBox.boxFourierSupport_eq_rectangularLatticeCoset`, `Langlands.RankinSelberg.RankOneBox.boxLatticeTest_fourierIntegral`, `Langlands.RankinSelberg.RankOneBox.boxLatticeTest_fourierPartner`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.

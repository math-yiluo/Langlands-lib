# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockLowerCompactFourier`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerCompactFourier` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockLowerCompactFourier`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockLowerCompactFourier` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Compact-uniform partial Fourier estimates for the lower integrand.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerDiagonalFourier`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding.partialSection_mul` (theorem): Moving the last factor of a group product into the Schwartz function.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding.exists_partialSection_diagonal_compact_bounds` (theorem): One pair of constants works for all compact right translates of the diagonal.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding.blockRotation_inv_mul_diagonal` (theorem): Moving the inverse block rotation through a diagonal permutes its entries.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding.exists_partialSection_rotated_diagonal_compact_bounds` (theorem): The compact-uniform row-factor bound in the representatives transported
  from the standard quotient.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding.exists_partialSection_rotated_torus_compact_bounds` (theorem): Specialization to the canonical uniformizer torus, with endpoint cutoffs
  at the adjacent standard coordinates on either side of the block cut.

Public declarations of the original that are not re-declared here: `Langlands.HarmonicAnalysis.finite_rowTranslate_schwartz_range`, `Langlands.RankinSelberg.TwoBlockLowerUnfolding.RotatedTorusBoundData`, `Langlands.RankinSelberg.TwoBlockLowerUnfolding.rotatedTorusBoundData`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.

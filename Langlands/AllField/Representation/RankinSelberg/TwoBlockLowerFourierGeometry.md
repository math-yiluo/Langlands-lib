# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockLowerFourierGeometry`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFourierGeometry` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockLowerFourierGeometry`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockLowerFourierGeometry` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Actual quotient geometry for lower Fourier transport**

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerUnipotentQuotientData`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockLowerFourier.ord_determinant_weylLong` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFourier.ord_determinant_dual` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFourier.lowerDuality_order` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFourier.lowerDuality_symm_order` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFourier.lowerDuality_slices` (theorem).

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.TwoBlockLowerFourier.blockRotation_reverse`, `Langlands.RankinSelberg.TwoBlockLowerFourier.inverseTranspose_blockRotation`, `Langlands.RankinSelberg.TwoBlockLowerFourier.weyl_conjugate_blockRotation`, `Langlands.RankinSelberg.TwoBlockLowerFourier.dual_rotation`, `Langlands.RankinSelberg.TwoBlockLowerFourier.reflectedGroup`, `Langlands.RankinSelberg.TwoBlockLowerFourier.reflectedGroup_apply`, `Langlands.RankinSelberg.TwoBlockLowerFourier.reflectedGroup_involutive`, `Langlands.RankinSelberg.TwoBlockLowerFourier.reflectedGroup_mem`, `Langlands.RankinSelberg.TwoBlockLowerFourier.standardDuality`, `Langlands.RankinSelberg.TwoBlockLowerFourier.standardDuality_mk`, `Langlands.RankinSelberg.TwoBlockLowerFourier.standardDuality_involutive`, `Langlands.RankinSelberg.TwoBlockLowerFourier.standardDuality_symm_mk`, `Langlands.RankinSelberg.TwoBlockLowerFourier.lowerDuality`, `Langlands.RankinSelberg.TwoBlockLowerFourier.lowerDuality_mk`, `Langlands.RankinSelberg.TwoBlockLowerFourier.lowerDuality_symm_mk`, `Langlands.RankinSelberg.TwoBlockLowerFourier.lowerDuality_conjugation`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.

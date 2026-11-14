# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockUnipotentCoordinates`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFirstBlockUnipotentCoordinates` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockUnipotentCoordinates`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockUnipotentCoordinates` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Block coordinates of the prescribed lower-unipotent Haar**

The prescribed Haar on `H⁻ = C⁻¹ N C` unfolds into the two diagonal unipotent
Haar measures and any supplied rectangular Haar, up to its integral-cube mass.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockQuotientUnfolding`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFirstBlockMeasureTransport`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.lintegral_lowerHaar_eq` (theorem): The prescribed lower-unipotent Haar is the inverse-conjugation transport of the
  standard full-unipotent Haar.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.lintegral_unipotentHaar_blockCoordinates` (theorem): The block coordinates `(b, Z) ↦ b u(Z)` of the standard full-unipotent Haar, for any
  two-block shape, with the fixed block measure unfolded into the two block Haar measures.
- `Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.lintegral_lowerHaar` (theorem): **Block coordinates of `H⁻`.** For every rectangular additive Haar `μR`,
  the integral-cube mass of `μR` times the prescribed lower-unipotent Haar integral
  equals the iterated integral over `diag(x, y) R(Z)` with `x ∈ N_a`, `y ∈ N_b`.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.reverseMatrix_mul_reverse_leviEmbedding`, `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.blockRotation_inv_mul_blockEmbedding_mul`, `Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient.blockRotation_inv_mul_coordinates_mul`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.

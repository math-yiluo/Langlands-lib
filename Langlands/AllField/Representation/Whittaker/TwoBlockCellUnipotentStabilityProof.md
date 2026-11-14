# All-field port of `Langlands.Representation.Whittaker.TwoBlockCellUnipotentStabilityProof`

`Langlands.AllField.Representation.Whittaker.TwoBlockCellUnipotentStabilityProof` is the all-field port of the Library module `Langlands.Representation.Whittaker.TwoBlockCellUnipotentStabilityProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.Whittaker.TwoBlockCellUnipotentStabilityProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Proof of the upper unipotent stability of the two-block cell submodule**

Read through the rank exchange `GL_(A+B) ≅ GL_(B+A)`, an upper unipotent `u`
lies in the standard parabolic of shape `(B, A)`, with diagonal blocks `α`, `δ`
and upper-right block `β`. Then `w n(x) u = diag(δ, α) w n(y)` with
`y = α⁻¹ (β + x δ)`. So right translation by `u` preserves the cell, and the
restriction of `ξ(u) f` is `ρ(diag(δ, α))` applied to the restriction of `f`
composed with the affine homeomorphism `x ↦ α⁻¹ (β + x δ)`.

## Imports from the port

- `Langlands.AllField.Representation.Whittaker.TwoBlockCellUnipotentStabilityStatement`

## Declarations

- `Langlands.AllField.Whittaker.exchangedParabolic` (def): The element `u` read in the parabolic of the exchanged shape `(B, A)`.
- `Langlands.AllField.Whittaker.swapRank_exchangedParabolic` (theorem).
- `Langlands.AllField.Whittaker.unipotentLeviFactor` (def): The Levi element `diag(δ, α)` of `P` attached to `u`.
- `Langlands.AllField.Whittaker.unipotentShift` (def): The coordinate change `x ↦ α⁻¹ (β + x δ)` attached to `u`.
- `Langlands.AllField.Whittaker.twoBlockCellPoint_mul_upperUnipotent` (theorem): `w n(x) u = diag(δ, α) w n(y)`, with `y` the shifted coordinate.
- `Langlands.AllField.Whittaker.mul_upperUnipotent_mem_twoBlockCell` (theorem): Right translation by an upper unipotent matrix preserves the cell.
- `Langlands.AllField.Whittaker.twoBlockCellUnipotentStability` (theorem): JPSS (9.1), upper unipotent stability: right translation by every upper
  unipotent matrix maps the cell submodule `D` into itself.

Public declarations of the original that are not re-declared here: `Langlands.Whittaker.parabolicDiagonal`, `Langlands.Whittaker.parabolicDiagonal_fst_apply`, `Langlands.Whittaker.parabolicDiagonal_snd_apply`, `Langlands.Whittaker.parabolicCorner`, `Langlands.Whittaker.parabolicShift`, `Langlands.Whittaker.upper_mul_parabolic`, `Langlands.Whittaker.blockWeyl_mul_intertwiningUnipotent_mul_swapRank`, `Langlands.Whittaker.blockSum_mem_twoBlocks_parabolic`, `Langlands.Whittaker.swapRank_symm_mem_parabolic`, `Langlands.Whittaker.affineHomeomorph`, `Langlands.Whittaker.affineHomeomorph_apply`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.

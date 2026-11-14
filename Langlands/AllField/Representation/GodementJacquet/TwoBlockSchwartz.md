# All-field port of `Langlands.Representation.GodementJacquet.TwoBlockSchwartz`

`Langlands.AllField.Representation.GodementJacquet.TwoBlockSchwartz` is the all-field port of the Library module `Langlands.Representation.GodementJacquet.TwoBlockSchwartz`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.GodementJacquet.TwoBlockSchwartz` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Upper-block integrals of full-matrix test functions**

For a Schwartz–Bruhat function `Φ` on `(t + 1) × (t + 1)` matrices, the upper-block
integral `Φ^P (A, D) = ∫ B, Φ [[A, B], [0, D]] dB` is Schwartz–Bruhat on
`Mat_{n₀} × Mat_{n₁}` and a finite sum of products. The integral of
`Φ (parabolicPoint z) * U z.1` over the parabolic parameters reduces to a Levi
integral of `Φ^P` with the radical factor `|det a|^(-n₁)`.

## Imports from the port

- `Langlands.AllField.Representation.GodementJacquet.TwoBlockParabolicHaar`

## Declarations

- `Langlands.AllField.GodementJacquet.TwoBlock.radicalWeight` (def): The radical factor `|det a|^(-n₁)` of a Levi element `L = (a, d)`.
- `Langlands.AllField.GodementJacquet.TwoBlock.integral_testFunction_parabolicPoint` (theorem): **Parabolic reduction of a full-matrix test function.** If, for every
  Schwartz–Bruhat `α` on `Mat_{n₀} × Mat_{n₁}`, the Levi function
  `L ↦ α (a, d) * (U L * |det a|^(-n₁))` is integrable, then
  `z ↦ Φ (parabolicPoint z) * U z.1` is integrable for the parabolic measure and its
  integral is the Levi integral of `Φ^P (a, d) * U L * |det a|^(-n₁)`.

Public declarations of the original that are not re-declared here: `Langlands.GodementJacquet.TwoBlock.upperBlockMap`, `Langlands.GodementJacquet.TwoBlock.upperBlockCoord`, `Langlands.GodementJacquet.TwoBlock.upperBlockCoord_upperBlockMap`, `Langlands.GodementJacquet.TwoBlock.parabolicPoint_val_eq_upperBlockMap`, `Langlands.GodementJacquet.TwoBlock.continuous_upperBlockMap`, `Langlands.GodementJacquet.TwoBlock.continuous_upperBlockCoord`, `Langlands.GodementJacquet.TwoBlock.upperBlockRestriction`, `Langlands.GodementJacquet.TwoBlock.upperBlockRestriction_apply`, `Langlands.GodementJacquet.TwoBlock.upperBlockIntegral`, `Langlands.GodementJacquet.TwoBlock.upperBlockIntegral_apply`, `Langlands.GodementJacquet.TwoBlock.exists_upperBlockIntegral_expansion`, `Langlands.GodementJacquet.TwoBlock.integrable_pi_two_mul`, `Langlands.GodementJacquet.TwoBlock.integral_pi_two_mul`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.

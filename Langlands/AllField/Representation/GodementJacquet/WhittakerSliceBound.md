# All-field port of `Langlands.Representation.GodementJacquet.WhittakerSliceBound`

`Langlands.AllField.Representation.GodementJacquet.WhittakerSliceBound` is the all-field port of the Library module `Langlands.Representation.GodementJacquet.WhittakerSliceBound`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.GodementJacquet.WhittakerSliceBound` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**The unipotent slice bound for matrix test functions**

For a full-matrix test function `Φ` and `k ∈ GL_(n+1)`, the integral of
`|Φ(u diag(a) k)|` over the upper unipotent group is at most a constant times a
monomial `∏ |a_i|^(-e_i)` times the characteristic function of a box. The module
also shows that the matrix integrand of a continuous function is measurable.
See the paired Markdown.

## Imports from the port

- `Langlands.AllField.Representation.GodementJacquet.Zeta`
- `Langlands.AllField.Representation.RankinSelberg.UnipotentDiagonalVolume`

## Declarations

- `Langlands.AllField.GodementJacquet.WhittakerTorus.Padic.normBox` (def): The box `{x | ∀ i, |x_i| ≤ ρ}` in `F^(n+1)`.
- `Langlands.AllField.GodementJacquet.WhittakerTorus.Padic.isClopen_normBox` (theorem).
- `Langlands.AllField.GodementJacquet.WhittakerTorus.Padic.isCompact_normBox` (theorem).
- `Langlands.AllField.GodementJacquet.WhittakerTorus.Padic.boxTest` (def): The characteristic function of `normBox`, as a Schwartz–Bruhat function.
- `Langlands.AllField.GodementJacquet.WhittakerTorus.Padic.boxTest_apply_of_le` (theorem).
- `Langlands.AllField.GodementJacquet.WhittakerTorus.Padic.torusMonomial` (def): The monomial `∏ |a_i|^(-e_i)` of the unipotent volume bound.
- `Langlands.AllField.GodementJacquet.WhittakerTorus.Padic.torusMonomial_nonneg` (theorem).
- `Langlands.AllField.GodementJacquet.WhittakerTorus.Padic.measurable_matrixIntegrand` (theorem).
- `Langlands.AllField.GodementJacquet.WhittakerTorus.Padic.exists_slice_bound` (theorem): **Slice bound.** For a test function `Φ` and `k ∈ GL_(n+1)`, the unipotent
  integral of `|Φ(u diag(a) k)|` is at most a constant times
  `∏ |a_i|^(-e_i)` times the characteristic function of a box.

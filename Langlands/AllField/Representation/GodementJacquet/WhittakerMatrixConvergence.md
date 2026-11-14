# All-field port of `Langlands.Representation.GodementJacquet.WhittakerMatrixConvergence`

`Langlands.AllField.Representation.GodementJacquet.WhittakerMatrixConvergence` is the all-field port of the Library module `Langlands.Representation.GodementJacquet.WhittakerMatrixConvergence`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.GodementJacquet.WhittakerMatrixConvergence` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Convergence of full-matrix Whittaker integrals**

Given `FiniteFunctionMellinStatement`, for `W` as in `IsWhittakerLike` and a
full-matrix test function `Φ`, the integral `∫ Φ(g) W(g) |det g|^s dg` converges
absolutely on a right half-plane. The proof uses Iwasawa integration, the finite
coset sum over `K`, the unipotent volume bound, and the torus Mellin integrals.
See the paired Markdown.

## Imports from the port

- `Langlands.AllField.Representation.GodementJacquet.WhittakerMatrixRationality`
- `Langlands.AllField.Representation.GodementJacquet.WhittakerSliceBound`

## Declarations

- `Langlands.AllField.GodementJacquet.WhittakerTorus.Padic.torusWeight` (def): The weight `δ(a)⁻¹ ∏ |a_i|^(-e_i)` as a complex function on the torus.
- `Langlands.AllField.GodementJacquet.WhittakerTorus.Padic.torusWeight_mul` (theorem).
- `Langlands.AllField.GodementJacquet.WhittakerTorus.Padic.continuous_torusWeight` (theorem).
- `Langlands.AllField.GodementJacquet.WhittakerTorus.Padic.isFiniteFunction_torusWeight` (theorem).
- `Langlands.AllField.GodementJacquet.WhittakerTorus.Padic.enorm_torusWeight` (theorem).
- `Langlands.AllField.GodementJacquet.WhittakerTorus.Padic.lintegral_torus_lt_top` (theorem): For `k ∈ K`, the torus integral of the unipotent integral of the matrix
  integrand at `u diag(a) k` is finite on a right half-plane.
- `Langlands.AllField.GodementJacquet.WhittakerTorus.Padic.IsWhittakerLike.matrixConverges` (theorem): **Convergence of full-matrix Whittaker integrals.** Given
  `FiniteFunctionMellinStatement`, for `W` as in `IsWhittakerLike` and a
  full-matrix test function `Φ`, the unshifted matrix integral
  `∫ Φ(g) W(g) |det g|^s dg` converges absolutely for `Re s` large.

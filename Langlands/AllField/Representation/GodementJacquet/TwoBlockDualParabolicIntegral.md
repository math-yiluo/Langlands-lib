# All-field port of `Langlands.Representation.GodementJacquet.TwoBlockDualParabolicIntegral`

`Langlands.AllField.Representation.GodementJacquet.TwoBlockDualParabolicIntegral` is the all-field port of the Library module `Langlands.Representation.GodementJacquet.TwoBlockDualParabolicIntegral`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.GodementJacquet.TwoBlockDualParabolicIntegral` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**The dual two-block parabolic integral**

Godement–Jacquet 1972, proof of Theorem 3.4 (printed pages 36–45): after the
substitution `g ↦ (g⁻¹)ᵀ`, the transformed zeta integral of an induced
representation is reduced to the Levi blocks along the coordinates
`(a, d, x) ↦ [[a, a x], [0, d]]` of the upper block parabolic. The inverse
transpose of this matrix is `[[(a⁻¹)ᵀ, 0], [-(d⁻¹)ᵀ xᵀ, (d⁻¹)ᵀ]]`, so the
radical variable `x` enters through the lower-left block. The substitution
`C = -(d⁻¹)ᵀ xᵀ` multiplies the rectangular Haar measure by `|det d|^(n₀)`, and
the lower-left partial integral of the test function then splits into the
Levi blocks.

This module proves that reduction for a test function whose lower-left partial
integral is a finite sum of tensor products, with weights `u₀, u₁` on the two
Levi blocks that are integrable against every Schwartz–Bruhat function composed
with the inverse transpose. Integrability on the product space comes from a
majorant by a product of indicators of compact open sets. The reduction is stated
both in the coordinates `((a, d), x)` and in Levi coordinates `(L, x)`. A last
section transfers finite decompositions of two-sided compact translates of a test
function to its Fourier transform evaluated at inverse transposes.

## Imports from the port

- `Langlands.AllField.HarmonicAnalysis.ConductorSupplement`
- `Langlands.AllField.HarmonicAnalysis.PadicLatticeTopology`
- `Langlands.AllField.HarmonicAnalysis.RectangularFourierUnimodularTranslate`
- `Langlands.AllField.Representation.RankinSelberg.EqualRankContinuedFormsProofSupplement`

## Declarations

- `Langlands.AllField.GodementJacquet.Padic.mulLeftMeasurableEquiv` (def): Left multiplication by an invertible matrix, as a measurable equivalence of
  rectangular matrices.
- `Langlands.AllField.GodementJacquet.Padic.mulLeftMeasurableEquiv_apply` (theorem).
- `Langlands.AllField.GodementJacquet.Padic.map_mulLeftMeasurableEquiv` (theorem): Left multiplication by `A` scales the rectangular measure by `|det A|^(-s)`.
- `Langlands.AllField.GodementJacquet.Padic.integral_comp_lowerLeft` (theorem): The lower-left substitution `C = -((d⁻¹)ᵀ xᵀ)` multiplies the rectangular measure
  by `|det d|^(n₀)`.
- `Langlands.AllField.GodementJacquet.Padic.integrable_comp_lowerLeft` (theorem): Integrability is preserved by the lower-left substitution.
- `Langlands.AllField.GodementJacquet.Padic.dualParabolicIntegrand` (def): The transformed integrand `Φ ([[a, a x], [0, d]]⁻ᵀ) u₀(a) u₁(d)` in the coordinates
  `((a, d), x)`, written through the block form
  `[[(a⁻¹)ᵀ, 0], [-(d⁻¹)ᵀ xᵀ, (d⁻¹)ᵀ]]` of the inverse transpose.
- `Langlands.AllField.GodementJacquet.Padic.measurable_inverseTranspose_val` (theorem).
- `Langlands.AllField.GodementJacquet.Padic.aestronglyMeasurable_dualParabolicIntegrand` (theorem): The transformed integrand is a.e. strongly measurable for every product measure
  for which the two Levi weights are.
- `Langlands.AllField.GodementJacquet.Padic.integrable_integral_dualParabolicIntegrand` (theorem): **Dual parabolic reduction.** Suppose the lower-left partial integral of `Φ` is a
  finite sum of tensor products `∑ₖ αₖ(x) βₖ(y)`, and that `a ↦ Ψ((a⁻¹)ᵀ) u₀(a)` and
  `d ↦ Ψ((d⁻¹)ᵀ) u₁(d) |det d|^(n₀)` are integrable for every Schwartz–Bruhat `Ψ`.
  Then the transformed integrand is integrable on `(GL_{n₀} × GL_{n₁}) × M_{n₀×n₁}`, and its
  integral is `∑ₖ (∫ αₖ((a⁻¹)ᵀ) u₀(a) da) (∫ βₖ((d⁻¹)ᵀ) u₁(d) |det d|^(n₀) dd)`.
- `Langlands.AllField.GodementJacquet.Padic.integrable_integral_dualParabolic_levi` (theorem): **Dual parabolic reduction in Levi coordinates.** Let `g (L, x)` be the matrix
  `[[L₀, L₀ x], [0, L₁]]` of the upper two-block parabolic, and integrate
  `Φ ((g⁻¹)ᵀ) u₀(L₀) u₁(L₁)` against `(∏ᵢ μᵢ) × dx`. If the lower-left partial integral of
  `Φ` is `∑ₖ αₖ(x) βₖ(y)`, the integrand is integrable and its integral is
  `∑ₖ (∫ αₖ((a⁻¹)ᵀ) u₀(a) da) (∫ βₖ((d⁻¹)ᵀ) u₁(d) |det d|^(m₀+1) dd)`.
- `Langlands.AllField.GodementJacquet.Padic.rectangularFourierEquiv_inverseTranspose_translate` (theorem): **Dual compact step.** If the two-sided translate `x ↦ Φ (A x B)` by matrices of
  normalized determinant one decomposes as `∑ₗ cₗ Φₗ`, then the Fourier transform of `Φ` at
  the inverse transpose of `A g B` decomposes with the same coefficients as
  `∑ₗ cₗ (FΦₗ)((g⁻¹)ᵀ)`.
- `Langlands.AllField.GodementJacquet.Padic.rectangularFourierEquiv_inverseTranspose_translate_of_mem` (theorem): The dual compact step for two elements of a compact subgroup of `GL_n`.

Public declarations of the original that are not re-declared here: `Langlands.GodementJacquet.measurable_matrix_transpose`, `Langlands.GodementJacquet.transposeMeasurableEquiv`, `Langlands.GodementJacquet.measurePreserving_transpose_rectangularMeasure`, `Langlands.GodementJacquet.inverseTranspose_val_of_upperBlock`, `Langlands.GodementJacquet.exists_isCompact_isClopen_superset`, `Langlands.GodementJacquet.exists_blockMatrix_majorant`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.

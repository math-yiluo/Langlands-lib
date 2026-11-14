# All-field port of `Langlands.Representation.GodementJacquet.WhittakerMatrixRationality`

`Langlands.AllField.Representation.GodementJacquet.WhittakerMatrixRationality` is the all-field port of the Library module `Langlands.Representation.GodementJacquet.WhittakerMatrixRationality`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.GodementJacquet.WhittakerMatrixRationality` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Rationality of full-matrix Whittaker integrals**

Given `FiniteFunctionMellinStatement` and convergence on a right half-plane,
the full-matrix integral `∫ Φ(g) W(g) |det g|^(s + t) dg` of a function `W`
with `IsWhittakerLike` has a rational continuation in `q^(-s)`. On a right
half-plane the integral is a finite linear combination of the torus integrals
of `WhittakerTorusMellin`. See the paired Markdown.

## Imports from the port

- `Langlands.AllField.Representation.GodementJacquet.WhittakerIwasawaReduction`

## Declarations

- `Langlands.AllField.GodementJacquet.WhittakerTorus.Padic.normalizedAbs_units_pos` (theorem): The normalized absolute value of a unit is positive.
- `Langlands.AllField.GodementJacquet.WhittakerTorus.Padic.normalizedAbs_prod_pos` (theorem): `|∏ a_i|` is positive.
- `Langlands.AllField.GodementJacquet.WhittakerTorus.Padic.normalizedAbs_prod_mul` (theorem): `|∏ a_i|` is multiplicative in `a`.
- `Langlands.AllField.GodementJacquet.WhittakerTorus.Padic.continuous_normalizedAbs_prod` (theorem): `a ↦ |∏ a_i|` is continuous.
- `Langlands.AllField.GodementJacquet.WhittakerTorus.Padic.borelModulus_pos` (theorem): The modulus `δ` is positive.
- `Langlands.AllField.GodementJacquet.WhittakerTorus.Padic.borelModulus_mul` (theorem): The modulus `δ` is multiplicative.
- `Langlands.AllField.GodementJacquet.WhittakerTorus.Padic.continuous_borelModulus` (theorem): The modulus `δ` is continuous.
- `Langlands.AllField.GodementJacquet.WhittakerTorus.Padic.twistedCharacter` (def): The function `χ(a) δ(a)⁻¹ |∏ a_i|^t` on the torus.
- `Langlands.AllField.GodementJacquet.WhittakerTorus.Padic.isFiniteFunction_twistedCharacter` (theorem): `χ δ⁻¹ |det|^t` is a finite function when `χ` is.
- `Langlands.AllField.GodementJacquet.WhittakerTorus.Padic.sliceTest` (def): The slice integral of `Φ(· k)`, as a Schwartz–Bruhat function on `F^(n+1)`.
- `Langlands.AllField.GodementJacquet.WhittakerTorus.Padic.sliceTest_apply` (theorem).
- `Langlands.AllField.GodementJacquet.WhittakerTorus.Padic.IsWhittakerLike.hasRationalContinuation` (theorem): **Rationality of full-matrix Whittaker integrals.** Assume
  `FiniteFunctionMellinStatement`, and let `W` satisfy `IsWhittakerLike`. If
  `∫ Φ(g) W(g) |det g|^s dg` converges absolutely on a right half-plane, then for
  every `t` the function `s ↦ ∫ Φ(g) W(g) |det g|^(s + t) dg` has a rational
  continuation in `q^(-s)`.

Public declarations of the original that are not re-declared here: `Langlands.GodementJacquet.WhittakerTorus.exists_common_halfPlane`, `Langlands.GodementJacquet.WhittakerTorus.exists_continuation_sum`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.

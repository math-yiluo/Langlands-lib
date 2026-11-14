# All-field port of `Langlands.Representation.GodementJacquet.WhittakerTorusMellin`

`Langlands.AllField.Representation.GodementJacquet.WhittakerTorusMellin` is the all-field port of the Library module `Langlands.Representation.GodementJacquet.WhittakerTorusMellin`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.GodementJacquet.WhittakerTorusMellin` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Torus Mellin integrals in diagonal coordinates**

Given `FiniteFunctionMellinStatement`, the torus integral
`∫ φ(a_0/a_1, …, a_(n-1)/a_n) J(a) η(a) |a_0 ⋯ a_n|^s da` converges on a right
half-plane and has a rational continuation in `q^(-s)`, for every finite
function `η` and Schwartz–Bruhat functions `φ` on `F^n` and `J` on `F^(n+1)`.
The proof changes variables by the tail products of
`WhittakerTorusCoordinates`. See the paired Markdown.

## Imports from the port

- `Langlands.AllField.Group.GL.NormalizedCharacterSupplement`
- `Langlands.AllField.Representation.RankinSelberg.AnalyticStatementSupplement`
- `Langlands.AllField.Representation.RankinSelberg.FiniteFunctionMellinStatement`

## Declarations

- `Langlands.AllField.GodementJacquet.WhittakerTorus.Padic.ratios` (def): Adjacent ratios `a_i / a_(i+1)` of diagonal entries, as field elements.
- `Langlands.AllField.GodementJacquet.WhittakerTorus.Padic.torusIntegrand` (def): The torus integrand `φ(ratios a) · J(a) · η(a) · |∏ a_i|^s`.
- `Langlands.AllField.GodementJacquet.WhittakerTorus.Padic.initTail` (def): The Schwartz–Bruhat function `y ↦ φ(y_0, …, y_(n-1)) · J(τ(y))`.
- `Langlands.AllField.GodementJacquet.WhittakerTorus.Padic.torusIntegrand_tailProd` (theorem): In tail-product coordinates the torus integrand is a finite-function Mellin
  integrand with weights `k + 1`.
- `Langlands.AllField.GodementJacquet.WhittakerTorus.Padic.torusMellin` (theorem): **Torus Mellin integrals.** Given `FiniteFunctionMellinStatement`, for a
  finite function `η` on the torus and Schwartz–Bruhat functions `φ` on `F^n`
  and `J` on `F^(n+1)`, the torus integral of `torusIntegrand` converges
  absolutely on a right half-plane and has a rational continuation in `q^(-s)`.

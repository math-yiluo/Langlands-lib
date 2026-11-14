# All-field port of `Langlands.Representation.GodementJacquet.SupercuspidalMatrixAssembly`

`Langlands.AllField.Representation.GodementJacquet.SupercuspidalMatrixAssembly` is the all-field port of the Library module `Langlands.Representation.GodementJacquet.SupercuspidalMatrixAssembly`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.GodementJacquet.SupercuspidalMatrixAssembly` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Supercuspidal matrix analytic data from the raw monomial equation**

## Imports from the port

- `Langlands.AllField.Representation.GodementJacquet.MatrixDenominatorCancellation`
- `Langlands.AllField.Representation.GodementJacquet.MatrixUnitValueProof`
- `Langlands.AllField.Representation.GodementJacquet.SupercuspidalMatrixRationality`

## Declarations

- `Langlands.AllField.GodementJacquet.Padic.HasMatrixMonomialFunctionalEquation` (def): The raw Fourier and monomial equation, without convergence, rational
  existence or normalized-generator assertions. Fourier witnesses precede every
  coefficient and both actual continuation guards are retained.
- `Langlands.AllField.GodementJacquet.Padic.SupercuspidalMatrixRationalityData.exists_laurent_value` (theorem): Every actual original continuation is Laurent once the raw monomial
  equation is supplied. Rational uniqueness transfers the common clearing to
  the continuation specified in the conclusion.
- `Langlands.AllField.GodementJacquet.Padic.SupercuspidalMatrixRationalityData.exists_laurent_iota_value` (theorem): Fourier surjectivity covers every dual test. Reflecting the raw rational
  identity transports the original Laurent value to its actual dual value.
- `Langlands.AllField.GodementJacquet.Padic.normalizedMatrixFunctionalEquationData_of_supercuspidal_of_monomial` (theorem): Actual irreducible supercuspidality supplies all analytic and generator
  assertions once the raw Fourier monomial functional equation is known.

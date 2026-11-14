# All-field port of `Langlands.Representation.GodementJacquet.SupercuspidalMatrixSmoothing`

`Langlands.AllField.Representation.GodementJacquet.SupercuspidalMatrixSmoothing` is the all-field port of the Library module `Langlands.Representation.GodementJacquet.SupercuspidalMatrixSmoothing`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.GodementJacquet.SupercuspidalMatrixSmoothing` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Compact coefficient smoothing of arbitrary matrix tests**

## Imports from the port

- `Langlands.AllField.Representation.GodementJacquet.SupercuspidalCutoffFourierRegularity`
- `Langlands.AllField.Representation.Induction.InverseTranspose`

## Declarations

- `Langlands.AllField.GodementJacquet.Padic.supercuspidalCutoffGroupTest` (def): The determinant-unit coefficient cutoff, restricted to the actual group.
- `Langlands.AllField.GodementJacquet.Padic.supercuspidalCutoffGroupTest_apply` (theorem).
- `Langlands.AllField.GodementJacquet.Padic.supercuspidalMatrixSmoothing` (def): Compact smoothing by the inverse cutoff, using the smooth representation
  on actual matrix Schwartz--Bruhat functions.
- `Langlands.AllField.GodementJacquet.Padic.supercuspidalMatrixSmoothing_apply` (theorem).
- `Langlands.AllField.GodementJacquet.Padic.supercuspidalMatrixSmoothing_right` (theorem): Determinant-unit translation of the coefficient vector becomes right
  matrix translation of the smoothed test.
- `Langlands.AllField.GodementJacquet.Padic.supercuspidalMatrixSmoothing_fourier_right` (theorem): Fourier evaluation obeys the inverse-transpose right covariance.
- `Langlands.AllField.GodementJacquet.Padic.supercuspidalMatrixSmoothing_singular` (theorem): Jacquet vanishing for the inverse-transpose pullback makes the original
  smoothed test vanish at every singular matrix.
- `Langlands.AllField.GodementJacquet.Padic.supercuspidalMatrixSmoothing_fourier_singular` (theorem): Jacquet vanishing of the original representation gives singular vanishing
  of the actual Fourier transform of every smoothed test.
- `Langlands.AllField.GodementJacquet.Padic.supercuspidalMatrixSmoothing_mem_fourierRegularMatrixTests` (theorem): Compact coefficient smoothing takes every matrix test, without any support
  restriction on that input, into the Fourier-regular test space.

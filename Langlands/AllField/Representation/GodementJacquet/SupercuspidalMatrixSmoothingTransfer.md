# All-field port of `Langlands.Representation.GodementJacquet.SupercuspidalMatrixSmoothingTransfer`

`Langlands.AllField.Representation.GodementJacquet.SupercuspidalMatrixSmoothingTransfer` is the all-field port of the Library module `Langlands.Representation.GodementJacquet.SupercuspidalMatrixSmoothingTransfer`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.GodementJacquet.SupercuspidalMatrixSmoothingTransfer` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Conjugate coefficient smoothing and bilinear transfer**

## Imports from the port

- `Langlands.AllField.Representation.GodementJacquet.InverseTransposeMatrixIntegral`
- `Langlands.AllField.Representation.GodementJacquet.SupercuspidalCutoffNonzeroOperator`
- `Langlands.AllField.Representation.GodementJacquet.SupercuspidalMatrixSmoothing`

## Declarations

- `Langlands.AllField.GodementJacquet.Padic.conjugateSupercuspidalCutoffGroupTest` (def): The complex conjugate of the actual compact coefficient cutoff on GL.
- `Langlands.AllField.GodementJacquet.Padic.conjugateSupercuspidalCutoffGroupTest_apply` (theorem).
- `Langlands.AllField.GodementJacquet.Padic.conjugateSupercuspidalCutoffGroupTest_eq_zero` (theorem).
- `Langlands.AllField.GodementJacquet.Padic.supercuspidalConjugateMatrixSmoothing` (def): Smoothing by the conjugate coefficient, defined through pointwise
  conjugation of the proved supercuspidal smoothing.
- `Langlands.AllField.GodementJacquet.Padic.supercuspidalConjugateMatrixSmoothing_eq_integratedAction` (theorem): This is the actual integrated action of the inverted conjugate cutoff.
- `Langlands.AllField.GodementJacquet.Padic.supercuspidalConjugateMatrixSmoothing_mem_fourierRegularMatrixTests` (theorem): Conjugated smoothing retains both singular-vanishing conditions.
- `Langlands.AllField.GodementJacquet.Padic.compactMatrixSmoothing_pairing` (theorem): A translation-compatible bilinear pairing commutes with compact smoothing
  on determinant norm one. The proof uses only finite-fiber integration.
- `Langlands.AllField.GodementJacquet.Padic.supercuspidalConjugateMatrixSmoothing_pairing` (theorem): Both continued zeta pairings can use this same integrated rho output.

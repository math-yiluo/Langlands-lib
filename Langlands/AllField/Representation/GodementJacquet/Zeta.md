# All-field port of `Langlands.Representation.GodementJacquet.Zeta`

`Langlands.AllField.Representation.GodementJacquet.Zeta` is the all-field port of the Library module `Langlands.Representation.GodementJacquet.Zeta`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.GodementJacquet.Zeta` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Godement–Jacquet matrix integrals and JPSS Section 5.2 value modules**

The test functions live on the full matrix space. The integral has exponent `s`;
the rational-value sets use `s + n/2` at actual rank `n + 1`. Convergence and
rational continuation are membership conditions, with no existence assertion.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.AnalyticStatementSupplement`

## Declarations

- `Langlands.AllField.GodementJacquet.Padic.matrixIntegrand` (def): The matrix integrand with the canonical residue-normalized absolute value.
- `Langlands.AllField.GodementJacquet.Padic.MatrixConverges` (def): Convergence for the shared Haar measure with integral general linear group
  of mass one, on the canonical p-adic topology and its Borel space.
- `Langlands.AllField.GodementJacquet.Padic.matrixIntegral` (def): The unshifted matrix integral with the shared normalized general-linear Haar measure.
- `Langlands.AllField.GodementJacquet.Padic.matrixRationalValues` (def): Shifted matrix-coefficient values with canonical topology, normalized absolute
  value, residue cardinality and the shared normalized Haar measure.
- `Langlands.AllField.GodementJacquet.Padic.whittakerRationalValues` (def): Shifted values from the actual model of the specified standard Whittaker
  functional, with the same canonical normalization as the matrix coefficients.
- `Langlands.AllField.GodementJacquet.Padic.jpssI2` (def): The canonical p-adic JPSS `I₂` Laurent module.
- `Langlands.AllField.GodementJacquet.Padic.jpssI3` (def): The canonical p-adic JPSS `I₃` Laurent module for the specified model.

Public declarations of the original that are not re-declared here: `Langlands.GodementJacquet.biSmoothCoefficient`, `Langlands.GodementJacquet.biSmoothMatrixCoefficients`, `Langlands.GodementJacquet.MatrixTestFunction`, `Langlands.GodementJacquet.matrixIntegrand`, `Langlands.GodementJacquet.MatrixConverges`, `Langlands.GodementJacquet.matrixIntegral`, `Langlands.GodementJacquet.jpssShift`, `Langlands.GodementJacquet.ShiftedConvergesOnRight`, `Langlands.GodementJacquet.HasShiftedRationalValue`, `Langlands.GodementJacquet.matrixRationalValues`, `Langlands.GodementJacquet.whittakerRationalValues`, `Langlands.GodementJacquet.jpssI2`, `Langlands.GodementJacquet.jpssI3`, `Langlands.GodementJacquet.jpssI2FractionalIdeal`, `Langlands.GodementJacquet.jpssI3FractionalIdeal`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.

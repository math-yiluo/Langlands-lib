# All-field port of `Langlands.Representation.RankinSelberg.UnequalRankBlockZeroContinuedFormsProof`

`Langlands.AllField.Representation.RankinSelberg.UnequalRankBlockZeroContinuedFormsProof` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.UnequalRankBlockZeroContinuedFormsProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Source: the original module `Langlands.Representation.RankinSelberg.UnequalRankBlockZeroContinuedFormsProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Continued unequal-rank bilinear forms at block zero**

Proof of `UnequalRankBlockZeroContinuedFormsStatement`. The two forms are the
evaluations at `q^{-s}` and `q^{-(1-s)}` of the bilinear families of rational
continuations of the original `(0,k)` integral and of the inverse-transpose
`(k,0)` integral of the dual model vectors. The finite exceptional set consists
of the roots of the original normalized generator and the reflections
`w ↦ (q w)⁻¹` of the roots of the dual normalized generator.

## Imports from the port

- `Langlands.AllField.Group.GL.CountabilityProof`
- `Langlands.AllField.Representation.RankinSelberg.EqualRankContinuedFormsProof`
- `Langlands.AllField.Representation.RankinSelberg.UnequalRankBlockZeroContinuedFormsStatement`

## Declarations

- `Langlands.AllField.RankinSelberg.padic_rectangular_laws` (theorem): The right-scaling and affine-invariance laws of the rectangular product
  measure built from any additive Haar measure, for the normalized absolute value.
- `Langlands.AllField.RankinSelberg.padic_quotient_sigmaFinite` (theorem): The supplied compatible quotient measure is sigma finite.
- `Langlands.AllField.RankinSelberg.unequalRankBlockZeroContinuedForms` (theorem): **Continued unequal-rank bilinear forms at block zero.** Proof of
  `UnequalRankBlockZeroContinuedFormsStatement`.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.matrixMulRightEquiv`, `Langlands.RankinSelberg.matrixMulLeftEquiv`, `Langlands.RankinSelberg.integral_comp_of_map_eq_smul`, `Langlands.RankinSelberg.integral_affine_eq_self`, `Langlands.RankinSelberg.spectralPoint_reflect`, `Langlands.RankinSelberg.dualBlockContinuationFamily`, `Langlands.RankinSelberg.dualBlockContinuationFamily_apply`, `Langlands.RankinSelberg.dualBlockContinuationFamily_clears`, `Langlands.RankinSelberg.dualBlockContinuationFamily_eq`, `Langlands.RankinSelberg.rectangularMeasure_zero_rows_translate`, `Langlands.RankinSelberg.blockZeroContinuedForms_of_laws`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.

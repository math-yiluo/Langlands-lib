# All-field port of `Langlands.Representation.Whittaker.CoordinateJacquetKernelProof`

`Langlands.AllField.Representation.Whittaker.CoordinateJacquetKernelProof` is the all-field port of the Library module `Langlands.Representation.Whittaker.CoordinateJacquetKernelProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Whittaker.CoordinateJacquetKernelProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Proof of uniform Whittaker vanishing on a coordinate Jacquet kernel**

Each generating relation `ρ u w - w` of the two-block Jacquet kernel has coefficient
`(ψ ((a_i / a_(i+1)) u_(i,i+1)) - 1) ℓ (ρ (torus a) w)` at the diagonal element
`torus a`. A positive normalized-absolute-value threshold kills the character factor,
and span induction combines finitely many thresholds by minima.

## Imports from the port

- `Langlands.AllField.HarmonicAnalysis.Conductor`
- `Langlands.AllField.Representation.Whittaker.CoordinateJacquetKernelStatement`

## Declarations

- `Langlands.AllField.Whittaker.CoordinateJacquetKernel.exists_pos_forall_addChar_eq_one` (theorem): A continuous unit-norm complex additive character is trivial on a ball of positive
  normalized-absolute-value radius around zero.
- `Langlands.AllField.Whittaker.CoordinateJacquetKernel.exists_pos_forall_addChar_mul_eq_one` (theorem): After multiplication by a fixed field element, the character is still trivial on a
  ball of positive normalized-absolute-value radius.
- `Langlands.AllField.Whittaker.CoordinateJacquetKernel.HasThreshold` (def): The threshold property of a vector, for one selected adjacent ratio.
- `Langlands.AllField.Whittaker.CoordinateJacquetKernel.thresholdSubmodule` (def): Vectors with a threshold form a submodule.
- `Langlands.AllField.Whittaker.CoordinateJacquetKernel.hasThreshold_relation` (theorem): The coordinate Whittaker conjugation identity and threshold for one generating relation
  of the two-block Jacquet kernel.
- `Langlands.AllField.Whittaker.CoordinateJacquetKernel.hasThreshold_of_jacquetMk_eq_zero` (theorem): Every vector of the actual two-block Jacquet kernel has a threshold.
- `Langlands.AllField.Whittaker.coordinateJacquetKernelStatement` (theorem): Uniform Whittaker vanishing on a coordinate Jacquet kernel.

Public declarations of the original that are not re-declared here: `Langlands.Whittaker.CoordinateJacquetKernel.torus`, `Langlands.Whittaker.CoordinateJacquetKernel.torus_val`, `Langlands.Whittaker.CoordinateJacquetKernel.torus_conj_apply`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.

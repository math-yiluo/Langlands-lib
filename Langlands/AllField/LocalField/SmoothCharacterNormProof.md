# All-field port of `Langlands.LocalField.SmoothCharacterNormProof`

`Langlands.AllField.LocalField.SmoothCharacterNormProof` is the all-field port of the Library module `Langlands.LocalField.SmoothCharacterNormProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.LocalField.SmoothCharacterNormProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Proof of the real norm decomposition of a smooth scalar character**

A character of `F^×` with open kernel has absolute value one on the norm-one
units, because these units form a compact group in which the kernel is an open
subgroup of finite index. Every unit is a norm-one unit times an integer power of
the specified uniformizer, so the absolute value of the character is
`‖ω ϖ‖ ^ ord a`, which is `|a| ^ c` for `c = -log_q ‖ω ϖ‖`. The exponent is
unique because `0 < |ϖ| = q⁻¹ < 1`.

## Imports from the port

- `Langlands.AllField.LocalField.Foundation`

## Declarations

- `Langlands.LocalFieldData.normalizedAbs_eq_one_iff_valuation_eq_one` (theorem): The residue-normalized absolute value is one exactly on the valuation-one locus.
- `Langlands.LocalFieldData.isCompact_normalizedAbs_eq_one_units` (theorem): The units of residue-normalized absolute value one are compact in the
  topology of units induced by the supplied field topology.

Public declarations of the original that are not re-declared here: `Langlands.PadicField.TopologicalData.norm_eq_one_of_normalizedAbs_eq_one`, `Langlands.PadicField.TopologicalData.norm_eq_norm_uniformizer_zpow_ord`, `Langlands.PadicField.TopologicalData.smoothCharacterNormDecomposition`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.

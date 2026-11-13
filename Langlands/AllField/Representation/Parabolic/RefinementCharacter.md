# All-field port of `Langlands.Representation.Parabolic.RefinementCharacter`

`Langlands.AllField.Representation.Parabolic.RefinementCharacter` is the all-field port of the Library module `Langlands.Representation.Parabolic.RefinementCharacter`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Parabolic.RefinementCharacter` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

The outer block modulus on an actual Levi refinement.

## Imports from the port

- `Langlands.AllField.Group.GL.BlockModulus`

## Declarations

- `Langlands.LocalFieldData.determinantNorm_refinedUnipotent` (theorem): Each outer component of a refined unipotent element has determinant norm one.
- `Langlands.LocalFieldData.refinedUnipotent_le_normOneLevi` (theorem): The whole refined radical lies in the simultaneous norm-one determinant subgroup.
- `Langlands.LocalFieldData.refinedUnipotent_le_ker_leviModulus` (theorem): The full outer modulus is trivial on the actual inner radical.
- `Langlands.LocalFieldData.leviModulus_refinedUnipotent` (theorem).
- `Langlands.LocalFieldData.leviHalfModulus_refinedUnipotent` (theorem): Thus the positive half used by outer induction is trivial on the inner radical.
- `Langlands.LocalFieldData.refinedOuterModulus` (def): The outer full modulus restricted to the actual refined Levi subgroup.
- `Langlands.LocalFieldData.refinedOuterModulus_apply` (theorem).
- `Langlands.LocalFieldData.refinedOuterHalfModulus` (def): The corresponding positive half, restricted using the same subgroup inclusion.
- `Langlands.LocalFieldData.refinedOuterHalfModulus_apply` (theorem).

Public declarations of the original that are not re-declared here: `Langlands.PadicField.TopologicalData.inverseHalfModulus_refinedUnipotent`, `Langlands.PadicField.TopologicalData.refinedOuterHalfModulus_eq`, `Langlands.PadicField.TopologicalData.refinedOuterHalfModulus_sq`, `Langlands.PadicField.TopologicalData.inverseHalf_refinedOuterModulus`, `Langlands.PadicField.TopologicalData.continuous_refinedOuterModulus`, `Langlands.PadicField.TopologicalData.isOpen_ker_refinedOuterModulus`, `Langlands.PadicField.TopologicalData.isOpen_ker_refinedOuterHalfModulus`, `Langlands.PadicField.TopologicalData.refinedOuterModulus_eq_topologicalData`, `Langlands.PadicField.TopologicalData.refinedOuterHalfModulus_eq_topologicalData`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.

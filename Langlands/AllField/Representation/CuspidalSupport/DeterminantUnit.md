# All-field port of `Langlands.Representation.CuspidalSupport.DeterminantUnit`

`Langlands.AllField.Representation.CuspidalSupport.DeterminantUnit` is the all-field port of the Library module `Langlands.Representation.CuspidalSupport.DeterminantUnit`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.CuspidalSupport.DeterminantUnit` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

The determinant-unit subgroup of a product Levi and smooth restriction.

## Imports from the port

- `Langlands.AllField.Group.GL.NormalizedCharacter`

## Declarations

- `Langlands.AllField.CuspidalSupport.leviDeterminantNorm` (def): The tuple of residue-normalized determinant absolute values, one per block.
- `Langlands.AllField.CuspidalSupport.leviDeterminantNorm_apply` (theorem).
- `Langlands.AllField.CuspidalSupport.determinantUnitSubgroup` (def): BZ76's `G°`: every block determinant has normalized absolute value one.
- `Langlands.AllField.CuspidalSupport.mem_determinantUnitSubgroup` (theorem).
- `Langlands.AllField.CuspidalSupport.mem_determinantUnitSubgroup_iff_normalizedAbs` (theorem).
- `Langlands.AllField.CuspidalSupport.determinantUnitSubgroup_normal` (instance).
- `Langlands.AllField.CuspidalSupport.determinantUnitInclusion` (abbrev): The actual inclusion of `G°` in the product Levi.
- `Langlands.AllField.CuspidalSupport.determinantUnitInclusion_apply` (theorem).
- `Langlands.AllField.CuspidalSupport.isOpen_determinantUnitSubgroup` (theorem): Openness follows from the finitely many open determinant kernels.
- `Langlands.AllField.CuspidalSupport.determinantUnitOpenSubgroup` (def): The same concrete subgroup packaged as an open subgroup.
- `Langlands.AllField.CuspidalSupport.continuous_determinantUnitInclusion` (theorem).
- `Langlands.AllField.CuspidalSupport.determinantUnitRestriction` (def): Restrict the actual action along the subgroup inclusion, retaining its carrier.
- `Langlands.AllField.CuspidalSupport.determinantUnitRestriction_apply` (theorem).
- `Langlands.AllField.CuspidalSupport.isSmooth_determinantUnitRestriction` (theorem).

Public declarations of the original that are not re-declared here: `Langlands.CuspidalSupport.determinantUnitSubgroup_eq`, `Langlands.CuspidalSupport.determinantUnitInclusion_injective`, `Langlands.CuspidalSupport.determinantUnitRestrictionMap`, `Langlands.CuspidalSupport.determinantUnitRestrictionMap_apply`, `Langlands.CuspidalSupport.determinantUnitRestrictionMap_id`, `Langlands.CuspidalSupport.determinantUnitRestrictionMap_comp`, `Langlands.CuspidalSupport.determinantUnitRestrictionFunctor`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.

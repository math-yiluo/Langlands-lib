# All-field port of `Langlands.Representation.CuspidalSupport.DualAveraging`

`Langlands.AllField.Representation.CuspidalSupport.DualAveraging` is the all-field port of the Library module `Langlands.Representation.CuspidalSupport.DualAveraging`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.CuspidalSupport.DualAveraging` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Averaging against smooth functionals, and compact open bases of product Levis**

A functional that is smooth for the dual action is unchanged by first averaging
over any compact open subgroup fixing it. Product Levis and their determinant-unit
subgroups have neighbourhood bases of compact open subgroups.

## Imports from the port

- `Langlands.AllField.Group.GL.BlockIwahoriBasis`
- `Langlands.AllField.Representation.CuspidalSupport.DeterminantUnit`

## Declarations

- `Langlands.AllField.CuspidalSupport.leviPiOpenSubgroup` (def): The product of open subgroups of the Levi factors, as an open subgroup.
- `Langlands.AllField.CuspidalSupport.mem_leviPiOpenSubgroup` (theorem).
- `Langlands.AllField.CuspidalSupport.isCompact_leviPiOpenSubgroup` (theorem).
- `Langlands.AllField.CuspidalSupport.exists_leviPiOpenSubgroup_subset` (theorem): Every identity neighbourhood of the product Levi contains a product of compact
  open subgroups, each with a block Iwahori factorization for the given refinement.
- `Langlands.AllField.CuspidalSupport.levi_exists_compact_openSubgroup_subset` (theorem): Compact open subgroups form a neighbourhood basis of `1` in the product Levi.

Public declarations of the original that are not re-declared here: `Langlands.Compact.dual_averageMap_eq_of_mem_fixedVectors`, `Langlands.Compact.exists_dual_averageMap_eq`, `Langlands.CuspidalSupport.determinantUnit_exists_compact_openSubgroup_subset`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.

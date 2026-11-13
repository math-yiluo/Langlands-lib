# All-field port of `Langlands.Group.GL.SingletonBlocks`

`Langlands.AllField.Group.GL.SingletonBlocks` is the all-field port of the Library module `Langlands.Group.GL.SingletonBlocks`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Group.GL.SingletonBlocks` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**The singleton block shape and the upper unipotent group**

With `n` blocks of size one, the standard block parabolic is the upper triangular
group and its unipotent radical is the actual upper unipotent group, with the same
matrices. Levi elements are diagonal matrices, and the block modulus is the
product of the root quotients `|t_i| / |t_j|` over `i < j`.

## Imports from the port

- `Langlands.AllField.Group.GL.BlockModulus`

## Declarations

- `Langlands.LocalFieldData.leviModulus_singletonLevi` (theorem): The singleton block modulus of a diagonal element is the product of the root
  quotients `|t_i| / |t_j|` over `i < j`.

Public declarations of the original that are not re-declared here: `Langlands.GeneralLinear.BlockShape.singletons`, `Langlands.GeneralLinear.BlockShape.singletons_length`, `Langlands.GeneralLinear.BlockShape.singletons_size`, `Langlands.GeneralLinear.BlockShape.singletons_size_neZero`, `Langlands.GeneralLinear.BlockShape.singletons_indexEquiv_apply`, `Langlands.GeneralLinear.BlockShape.singletons_index`, `Langlands.GeneralLinear.BlockShape.singletons_mem_parabolic_iff`, `Langlands.GeneralLinear.BlockShape.singletons_unipotentSubgroup`, `Langlands.GeneralLinear.BlockShape.singletons_mem_unipotentRadical_iff`, `Langlands.GeneralLinear.BlockShape.upperUnipotentEquivRadical`, `Langlands.GeneralLinear.BlockShape.upperUnipotentEquivRadical_apply_val`, `Langlands.GeneralLinear.BlockShape.upperUnipotentEquivRadical_symm_apply_val`, `Langlands.GeneralLinear.BlockShape.upperUnipotentContinuousEquivRadical`, `Langlands.GeneralLinear.BlockShape.upperUnipotentContinuousEquivRadical_toMulEquiv`, `Langlands.GeneralLinear.BlockShape.upperUnipotentContinuousEquivRadical_apply`, `Langlands.GeneralLinear.BlockShape.singletonLevi`, `Langlands.GeneralLinear.BlockShape.singletonLevi_apply`, `Langlands.GeneralLinear.BlockShape.leviEmbedding_singletonLevi_val`, `Langlands.GeneralLinear.BlockShape.leviAction_apply_val`, `Langlands.GeneralLinear.BlockShape.leviAction_singletonLevi_upperUnipotentEquivRadical`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.

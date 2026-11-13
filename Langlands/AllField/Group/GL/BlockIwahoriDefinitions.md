# All-field port of `Langlands.Group.GL.BlockIwahoriDefinitions`

`Langlands.AllField.Group.GL.BlockIwahoriDefinitions` is the all-field port of the Library module `Langlands.Group.GL.BlockIwahoriDefinitions`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Group.GL.BlockIwahoriDefinitions` in the Library. Its Markdown file gives the literature provenance of each statement.

## Imports from the port

- `Langlands.AllField.Group.GL.NormalizedCharacter`

## Declarations

- `Langlands.AllField.GeneralLinear.BlockShape.blockScalarRatio` (def): The actual root-ratio character in block-scalar coordinates.
- `Langlands.AllField.GeneralLinear.BlockShape.blockScalarRatio_apply` (theorem).
- `Langlands.AllField.GeneralLinear.BlockShape.IsWeaklyContracting` (def): Weak contraction of the upper radical: every forward block ratio is at most one.
- `Langlands.AllField.GeneralLinear.BlockShape.IsStrictlyContracting` (def): Strict contraction of the upper radical: every forward block ratio is below one.
- `Langlands.AllField.GeneralLinear.BlockShape.IsDeeplyContracting` (def): The ratio inequalities alone; consumers separately impose `0 < ε` and `ε ≤ 1`.
- `Langlands.AllField.GeneralLinear.BlockShape.isWeaklyContracting_one` (theorem).
- `Langlands.AllField.GeneralLinear.BlockShape.IsStrictlyContracting.weak` (theorem).
- `Langlands.AllField.GeneralLinear.BlockShape.IsDeeplyContracting.strict` (theorem).
- `Langlands.AllField.GeneralLinear.BlockShape.IsWeaklyContracting.mul` (theorem).
- `Langlands.AllField.GeneralLinear.BlockShape.HasBlockIwahoriFactorization` (def): A weak-chamber version of block Iwahori factorization for an actual open subgroup.
  Compactness is deliberately a separate `IsCompact (K : Set _)` hypothesis.

Public declarations of the original that are not re-declared here: `Langlands.GeneralLinear.BlockShape.blockScalarLevi`, `Langlands.GeneralLinear.BlockShape.blockScalarInLevi`, `Langlands.GeneralLinear.BlockShape.blockScalar`, `Langlands.GeneralLinear.BlockShape.blockScalarLevi_apply`, `Langlands.GeneralLinear.BlockShape.blockScalarInLevi_val`, `Langlands.GeneralLinear.BlockShape.blockScalar_one`, `Langlands.GeneralLinear.BlockShape.blockScalar_mul`, `Langlands.GeneralLinear.BlockShape.blockScalar_inv`, `Langlands.GeneralLinear.BlockShape.blockScalar_apply_same`, `Langlands.GeneralLinear.BlockShape.blockScalar_apply_ne`, `Langlands.GeneralLinear.BlockShape.blockScalar_mem_leviSubgroup`, `Langlands.GeneralLinear.BlockShape.blockScalarLevi_commute`, `Langlands.GeneralLinear.BlockShape.blockScalar_conj_mem_unipotentSubgroup`, `Langlands.GeneralLinear.BlockShape.blockScalar_inv_conj_mem_oppositeUnipotentSubgroup`, `Langlands.GeneralLinear.BlockShape.coe_blockScalar`, `Langlands.GeneralLinear.BlockShape.blockScalar_mul_apply`, `Langlands.GeneralLinear.BlockShape.mul_blockScalar_apply`, `Langlands.GeneralLinear.BlockShape.blockScalar_conj_apply`, `Langlands.GeneralLinear.BlockShape.blockScalar_inv_conj_apply`, `Langlands.GeneralLinear.BlockShape.iwahoriLower`, `Langlands.GeneralLinear.BlockShape.iwahoriLevi`, `Langlands.GeneralLinear.BlockShape.iwahoriUpper`, `Langlands.GeneralLinear.BlockShape.mem_iwahoriLower`, `Langlands.GeneralLinear.BlockShape.mem_iwahoriLevi`, `Langlands.GeneralLinear.BlockShape.mem_iwahoriUpper`, `Langlands.GeneralLinear.BlockShape.iwahoriProduct`, `Langlands.GeneralLinear.BlockShape.iwahoriProduct_val`, `Langlands.GeneralLinear.BlockShape.iwahoriProduct_one`, `Langlands.GeneralLinear.BlockShape.isWeaklyContracting_const`, `Langlands.GeneralLinear.BlockShape.isDeeplyContracting_of_length_le_one`, `Langlands.GeneralLinear.BlockShape.HasBlockIwahoriFactorization.bijective`, `Langlands.GeneralLinear.BlockShape.HasBlockIwahoriFactorization.upper_conj_mem`, `Langlands.GeneralLinear.BlockShape.HasBlockIwahoriFactorization.lower_inv_conj_mem`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.

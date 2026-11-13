# All-field port of `Langlands.Group.GL.BlockContractionProof`

`Langlands.AllField.Group.GL.BlockContractionProof` is the all-field port of the Library module `Langlands.Group.GL.BlockContractionProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Except for the changes described under Proof route below, each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

The original uses the canonical normed-field structure `F.canonicalNormedField` of the p-adic field, and transports a supplied realization to it (`topology_eq_canonical…`). The port uses the supplied data `T : LocalFieldData F` throughout. Where the original quantifies over a p-adic field with its canonical data, the port quantifies over a field `F` and arbitrary data `T`. The transport is then unnecessary and is omitted.

Source: the original module `Langlands.Group.GL.BlockContractionProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Proof route

One proof differs from the original: `uniformCompactBlockContraction` no longer uses the canonical norm of a finite extension of the p-adic numbers. Instead the private definition `absNormedField` equips `F` with the normed-field structure whose norm is `T.normalizedAbs` (multiplicative, and ultrametric by `normalizedAbs_add_le_max`), and the private lemma `topology_eq_absNormTopology` shows that its metric topology is `T.topology`, because the normalized-absolute-value balls are a neighbourhood basis (`hasBasis_nhds_normalizedAbs`). The rest of the argument is the original one: an open neighbourhood of the identity contains every matrix `g` with `‖g - 1‖ < δ` and `‖g⁻¹ - 1‖ < δ`; compact sets of matrices are norm bounded by some `M`; and conjugating a radical element by a block scalar multiplies its off-diagonal blocks by the ratios `a i * (a j)⁻¹`. Since the norm is now the normalized absolute value itself, the depth bound is `min 1 (δ / M)` rather than its power by the extension degree.

## Imports from the port

- `Langlands.AllField.Group.GL.BlockContractionStatement`

## Declarations

- `Langlands.AllField.GeneralLinear.BlockShape.strictPowersEventuallyDeep` (theorem).
- `Langlands.AllField.GeneralLinear.BlockShape.deepChamberNonempty` (theorem).
- `Langlands.AllField.GeneralLinear.BlockShape.uniformCompactBlockContraction` (theorem).
- `Langlands.AllField.GeneralLinear.BlockShape.strictPowers_eventually_mem_iwahori` (theorem): High powers of any strict scalar carry radical elements into any open subgroup's
  corresponding radical intersections. No factorization or compactness of the subgroup is needed.

Public declarations of the original that are not re-declared here: `Langlands.GeneralLinear.BlockShape.blockContraction`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.

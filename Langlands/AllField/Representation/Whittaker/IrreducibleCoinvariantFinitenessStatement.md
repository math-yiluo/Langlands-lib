# All-field port of `Langlands.Representation.Whittaker.IrreducibleCoinvariantFinitenessStatement`

`Langlands.AllField.Representation.Whittaker.IrreducibleCoinvariantFinitenessStatement` is the all-field port of the Library module `Langlands.Representation.Whittaker.IrreducibleCoinvariantFinitenessStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Whittaker.IrreducibleCoinvariantFinitenessStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Finite twisted upper-unipotent coinvariants of irreducible representations**

The finiteness assertion of Bernstein--Zelevinsky (1976), Theorem 5.21, printed
p.51, for `GL_n` over a nonarchimedean local field `F` with supplied data
`T : LocalFieldData F`. This is a proposition definition, not a
proof.

## Imports from the port

- `Langlands.AllField.LocalField.Foundation`

## Declarations

- `Langlands.AllField.Whittaker.IrreducibleCoinvariantFinitenessStatement` (def): For an irreducible smooth complex representation of the actual `GL_n(F)`
  and every locally constant character of the actual upper-unipotent subgroup,
  the actual character-localized coinvariant quotient is finite-dimensional.
  The supplied topological data determines smoothness and local constancy;
  `n = 0` is allowed.

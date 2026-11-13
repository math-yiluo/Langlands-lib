# All-field port of `Langlands.Representation.Whittaker.MirabolicFiniteLengthStatement`

`Langlands.AllField.Representation.Whittaker.MirabolicFiniteLengthStatement` is the all-field port of the Library module `Langlands.Representation.Whittaker.MirabolicFiniteLengthStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Whittaker.MirabolicFiniteLengthStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Finite length of restriction to the actual mirabolic subgroup**

Bernstein--Zelevinsky (1976), Corollary 5.22, printed p.51, implication (1)
implies (2), for `GL_n` over a nonarchimedean local field `F` with supplied data
`T : LocalFieldData F`. This is a proposition definition,
not a proof.

## Imports from the port

- `Langlands.AllField.LocalField.Foundation`

## Declarations

- `Langlands.AllField.Whittaker.MirabolicFiniteLengthStatement` (def): A smooth complex representation of `GL_(n+1)(F)` of finite length remains
  of finite length upon restriction along the actual mirabolic inclusion.
  The supplied topological data determines smoothness; `n = 0` is allowed.

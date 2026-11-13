# All-field port of `Langlands.Representation.Whittaker.JPSUniformDilationStatement`

`Langlands.AllField.Representation.Whittaker.JPSUniformDilationStatement` is the all-field port of the Library module `Langlands.Representation.Whittaker.JPSUniformDilationStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Whittaker.JPSUniformDilationStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Uniform small-coordinate dilation for actual JPS function spaces**

The small-coordinate dilation step in the proof of JPS (1979), Lemma (2.2.1),
for the actual function spaces and coordinate-germ quotients of
`Langlands.Whittaker.JPSFunctionSpace`. This module defines a proposition only.

## Imports from the port

- `Langlands.AllField.Representation.Whittaker.JPSFunctionSpace`

## Declarations

- `Langlands.AllField.Whittaker.JPSUniformDilationStatement` (def): JPS (1979), proof of Lemma (2.2.1): from local constancy and a finite
  coordinate operator span alone, one finite set `Y` of finite functions on `Fˣ`
  and one operator family `A` in the span of the bounded coordinate dilations
  `ρ_i(b)`, `|b| ≤ 1`, both chosen before every function, expand the action
  `σ_i(b)` on the actual germ quotient for every `b`. For each `f`, one positive
  threshold, chosen before the whole torus tuple and every `b` with `|b| ≤ 1`,
  makes the expansion of `ρ_i(b) f` hold pointwise below it.

# All-field port of `Langlands.Representation.Whittaker.JPSDilationAssemblyStatement`

`Langlands.AllField.Representation.Whittaker.JPSDilationAssemblyStatement` is the all-field port of the Library module `Langlands.Representation.Whittaker.JPSDilationAssemblyStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Whittaker.JPSDilationAssemblyStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**JPS decomposition assembly from uniform coordinate dilations**

An internal conditional assembly step for JPS (1979), Lemma (2.2.1). This module
defines a proposition only.

## Imports from the port

- `Langlands.AllField.Representation.Whittaker.JPSFunctionSpace`

## Declarations

- `Langlands.AllField.Whittaker.JPSDilationAssemblyStatement` (def): Internal assembly helper for JPS (1979), Lemma (2.2.1): let `W` be a
  translation-stable space of locally constant functions on `H = (Fˣ)ⁿ` with
  coordinate upper support. Suppose that, in every coordinate `i`, one finite set
  `Y i` of finite functions on `Fˣ` and one family `A i` of linear endomorphisms of
  `W`, both chosen before every function, expand every bounded dilation
  `b ↦ f (a * coordinateEmbedding i b)` with `|b| ≤ 1` on a region `|a_i| < ε`,
  whose threshold depends on `f` but precedes the whole tuple `a` and all such `b`.
  Then one finite set `X` of finite functions on `H`, chosen before the function,
  expands every `f` in `W` with Schwartz–Bruhat coefficients on the whole additive
  space `Fⁿ`. This is an internal derived target, not a printed JPS theorem.

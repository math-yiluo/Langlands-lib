# All-field port of `Langlands.Representation.Whittaker.JPSDecompositionStatement`

`Langlands.AllField.Representation.Whittaker.JPSDecompositionStatement` is the all-field port of the Library module `Langlands.Representation.Whittaker.JPSDecompositionStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Whittaker.JPSDecompositionStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**JPS function-space decomposition**

The full conclusion of JPS (1979), Lemma (2.2.1), for the actual function spaces
and coordinate-germ quotients of `Langlands.Whittaker.JPSFunctionSpace`. This is
a proposition definition, not a proof.

## Imports from the port

- `Langlands.AllField.Representation.Whittaker.JPSFunctionSpace`

## Declarations

- `Langlands.AllField.Whittaker.JPSDecompositionStatement` (def): JPS (1979), Lemma (2.2.1): let `W` be a translation-stable space of locally
  constant functions on `H = (Fˣ)ⁿ`, each vanishing when one coordinate is large,
  uniformly in the others, such that every coordinate action `σ_i` on the actual
  quotient `W / W_i` spans a finite-dimensional operator space. Then one finite set
  `X` of finite functions on `H`, chosen before the function, expands every `f` in
  `W` with Schwartz–Bruhat coefficients on the whole additive space `Fⁿ`.

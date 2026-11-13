# All-field port of `Langlands.Representation.Whittaker.JPSDecompositionProof`

`Langlands.AllField.Representation.Whittaker.JPSDecompositionProof` is the all-field port of the Library module `Langlands.Representation.Whittaker.JPSDecompositionProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). The original module does not name `PadicField` itself; the p-adic field enters through the statements that it proves or uses. In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Whittaker.JPSDecompositionProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Proof of the JPS function-space decomposition**

The published uniform dilation theorem supplies each coordinate's finite family
before the function is chosen. The published assembly theorem then gives the
uniform finite family on the full torus with Schwartz–Bruhat coefficients.

## Imports from the port

- `Langlands.AllField.Representation.Whittaker.JPSDecompositionStatement`
- `Langlands.AllField.Representation.Whittaker.JPSDilationAssemblyProof`
- `Langlands.AllField.Representation.Whittaker.JPSUniformDilationProof`

## Declarations

- `Langlands.AllField.Whittaker.jpsDecomposition` (theorem): JPS (1979), Lemma (2.2.1), with one finite family for the entire function
  space and Schwartz–Bruhat coefficients on the whole additive space.

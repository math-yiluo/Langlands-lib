# All-field port of `Langlands.Representation.Derivative.MirabolicMinusIrreducibleStatement`

`Langlands.AllField.Representation.Derivative.MirabolicMinusIrreducibleStatement` is the all-field port of the Library module `Langlands.Representation.Derivative.MirabolicMinusIrreducibleStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Derivative.MirabolicMinusIrreducibleStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Irreducibility of unnormalized `Φ⁻`**

The unnormalized Bernstein–Zelevinsky functor `Φ⁻ : P_(m+2) → P_(m+1)` sends an
irreducible smooth representation to an irreducible representation or to zero.

## Imports from the port

- `Langlands.AllField.Representation.Derivative.MirabolicMinus`

## Declarations

- `Langlands.AllField.Derivative.Mirabolic.PhiMinusIrreducibleStatement` (def): For an irreducible smooth representation `ξ` of `mirabolic (m + 1) F`, every
  subrepresentation of the unnormalized `Φ⁻ ξ` is `⊥` or `⊤`: the representation
  `Φ⁻ ξ` of `mirabolic m F` is irreducible or zero.

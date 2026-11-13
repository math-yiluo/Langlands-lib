# All-field port of `Langlands.HarmonicAnalysis.PadicRowFourierCutoffStatement`

`Langlands.AllField.HarmonicAnalysis.PadicRowFourierCutoffStatement` is the all-field port of the Library module `Langlands.HarmonicAnalysis.PadicRowFourierCutoffStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Source: the original module `Langlands.HarmonicAnalysis.PadicRowFourierCutoffStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Simultaneous normalized local-field row Fourier cutoffs**

This is a proposition target, not a proof. One pair of actual Schwartz--Bruhat
row functions is both a large cutoff, equal to one on a prescribed compact set,
and the plus-sign Fourier preimage of a small cutoff of total mass one, for
every supplied scalar Haar measure that is self-dual for the character.

## Imports from the port

- `Langlands.AllField.LocalField.Foundation`

## Declarations

- `Langlands.AllField.HarmonicAnalysis.PadicRowFourierCutoffStatement` (def): For a self-dual supplied scalar Haar measure, every compact set of rows and
  every open neighbourhood of zero admit one even Fourier pair `(Φ, κ)`: the
  plus-sign row transform of `Φ` is `κ`, `Φ` is one on the compact set, `κ` is
  supported in the neighbourhood and has integral exactly one for the product
  of the supplied measure. This includes dimension zero.

Public declarations of the original that are not re-declared here: `Langlands.HarmonicAnalysis.rowFourierCutoff_nonarchimedean`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.

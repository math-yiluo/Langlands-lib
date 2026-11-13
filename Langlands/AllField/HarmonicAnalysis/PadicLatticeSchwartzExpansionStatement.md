# All-field port of `Langlands.HarmonicAnalysis.PadicLatticeSchwartzExpansionStatement`

`Langlands.AllField.HarmonicAnalysis.PadicLatticeSchwartzExpansionStatement` is the all-field port of the Library module `Langlands.HarmonicAnalysis.PadicLatticeSchwartzExpansionStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Source: the original module `Langlands.HarmonicAnalysis.PadicLatticeSchwartzExpansionStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

A focused single-level lattice-coset expansion target for scalar local-field test functions.

## Imports from the port

- `Langlands.AllField.HarmonicAnalysis.Conductor`

## Declarations

- `Langlands.AllField.HarmonicAnalysis.PadicLatticeSchwartzExpansionStatement` (def): Every Schwartz–Bruhat function on a supplied nonarchimedean local field is, at every point,
  a finite complex linear combination of indicators of cosets `a i + π^(-m) O`
  of one common valuation lattice. All finite data are chosen before the point.

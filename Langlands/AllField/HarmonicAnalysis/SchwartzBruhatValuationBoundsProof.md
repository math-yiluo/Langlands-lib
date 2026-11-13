# All-field port of `Langlands.HarmonicAnalysis.SchwartzBruhatValuationBoundsProof`

`Langlands.AllField.HarmonicAnalysis.SchwartzBruhatValuationBoundsProof` is the all-field port of the Library module `Langlands.HarmonicAnalysis.SchwartzBruhatValuationBoundsProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.HarmonicAnalysis.SchwartzBruhatValuationBoundsProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Valuation cutoffs and uniform bounds for scalar Schwartz–Bruhat functions: proof**

The normalized absolute value is continuous for the supplied topology, and every
neighbourhood of zero contains a normalized ball around zero. Compact support then
bounds the normalized absolute value on the support, and local constancy at zero
gives a ball on which the function equals its value at zero.

## Imports from the port

- `Langlands.AllField.HarmonicAnalysis.SchwartzBruhatValuationBoundsStatement`

## Declarations

- `Langlands.LocalFieldData.exists_normalizedAbs_ball_subset` (theorem): Every neighbourhood of zero for the supplied topology contains a normalized ball
  around zero.
- `Langlands.AllField.HarmonicAnalysis.schwartzBruhatValuationBounds` (theorem): Every scalar Schwartz–Bruhat function on a supplied nonarchimedean local field is bounded,
  vanishes on units of sufficiently negative order and equals its value at zero on
  units of sufficiently large order.

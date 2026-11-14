# All-field port of `Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffStatement`

`Langlands.AllField.Representation.RankinSelberg.ZeroRowLastRowCutoffStatement` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Compact last-row cutoff for smooth zero-row Whittaker coefficients**

This proposition isolates the compact-support input to JPSS Section 8.3.
The smooth coefficient-image scope and the zero-or-one cutoff are a derived
internal formulation, as explained in the paired Markdown.

## Imports from the port

- `Langlands.AllField.Group.GL.PadicSupplement`

## Declarations

- `Langlands.AllField.RankinSelberg.ZeroRowLastRowCutoffStatement` (def): Every coefficient in a smooth Whittaker coefficient image admits a
  zero-or-one Schwartz–Bruhat cutoff on the last row that leaves its zero-row
  restriction unchanged. This is a closed proposition definition, not a proof.

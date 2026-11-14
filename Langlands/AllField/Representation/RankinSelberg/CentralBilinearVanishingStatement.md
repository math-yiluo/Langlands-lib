# All-field port of `Langlands.Representation.RankinSelberg.CentralBilinearVanishingStatement`

`Langlands.AllField.Representation.RankinSelberg.CentralBilinearVanishingStatement` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.CentralBilinearVanishingStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.CentralBilinearVanishingStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Finite spectral support of twisted bilinear forms**

This proposition defines an internal central-polynomial formulation of the
residual bilinear obstruction in JPSS Section 2.10, printed page 398.
It is a statement, not a proof.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.AnalyticStatementSupplement`

## Declarations

- `Langlands.AllField.RankinSelberg.CentralBilinearVanishingStatement` (def): Outside one finite set of spectral values, every determinant-twisted
  bilinear form on two admissible finite-type representations of positive-rank
  GL vanishes. The exceptional set is chosen before the parameter and form.

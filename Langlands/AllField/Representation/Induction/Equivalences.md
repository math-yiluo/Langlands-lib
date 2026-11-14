# All-field port of `Langlands.Representation.Induction.Equivalences`

`Langlands.AllField.Representation.Induction.Equivalences` is the all-field port of the Library module `Langlands.Representation.Induction.Equivalences`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Induction.Equivalences` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Transport of smooth induction along representation equivalences**

Postcomposition by an equivalence transports smooth induced functions, including
between independent carrier universes. Normalized parabolic induction specializes
this construction after inflation and the common character twist.

## Imports from the port

- `Langlands.AllField.Representation.Induction.Parabolic`

## Declarations

- `Langlands.LocalFieldData.normalizedParabolicInducedMap_injective` (theorem): An injective Levi map remains injective after normalized parabolic induction.
- `Langlands.LocalFieldData.normalizedParabolicInducedEquiv` (def): Normalize, inflate, and induce an actual Levi equivalence. The two Levi
  representation carriers may lie in independent universes.
- `Langlands.LocalFieldData.normalizedParabolicInducedEquiv_eval` (theorem).

Public declarations of the original that are not re-declared here: `Langlands.Induction.smoothInducedMap_injective`, `Langlands.Induction.smoothInducedEquiv`, `Langlands.Induction.smoothInducedEquiv_eval`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.

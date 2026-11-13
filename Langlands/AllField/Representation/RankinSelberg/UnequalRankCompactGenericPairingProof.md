# All-field port of `Langlands.Representation.RankinSelberg.UnequalRankCompactGenericPairingProof`

`Langlands.AllField.Representation.RankinSelberg.UnequalRankCompactGenericPairingProof` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.UnequalRankCompactGenericPairingProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.UnequalRankCompactGenericPairingProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Proof of the unequal-rank compact generic pairing statement**

The covariant pairing space between the compact mirabolic model of rank `r + 1` and an
admissible irreducible generic representation of `GL_(n+1)` is a complex line for every
exponent. This combines the conditional result
`unequalRankCompactGenericPairing_of_multiplicityOne` with the Library proof of
Whittaker multiplicity one.

## Imports from the port

- `Langlands.AllField.Group.GL.CountabilityProof`
- `Langlands.AllField.Representation.RankinSelberg.UnequalRankCompactPairingMultiplicity`

## Declarations

- `Langlands.AllField.RankinSelberg.unequalRankCompactGenericPairing` (theorem): The unequal-rank compact generic pairing space has exact dimension one.

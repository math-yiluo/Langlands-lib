# All-field port of `Langlands.Representation.Whittaker.MirabolicPairingStatement`

`Langlands.AllField.Representation.Whittaker.MirabolicPairingStatement` is the all-field port of the Library module `Langlands.Representation.Whittaker.MirabolicPairingStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Whittaker.MirabolicPairingStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Irreducible mirabolic functionals and twisted pairings**

Proposition targets for the consequences of JPSS (1983), Proposition 1.4 and
Section 1.5, used in Section 2.10. No classification or proof is asserted here.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.AnalyticStatement`

## Declarations

- `Langlands.AllField.Whittaker.MirabolicFunctionalMultiplicityStatement` (def): JPSS Section 1.5, Corollary 1: scalar uniqueness of the full character
  functional space, recognition of the compact standard representation by a
  linear equivalence with `ℂ`, and vanishing for every other irreducible.

Public declarations of the original that are not re-declared here: `Langlands.Whittaker.MirabolicTwistedPairingRigidityStatement`, `Langlands.Whittaker.MirabolicCompactTwistedPairingStatement`, `Langlands.Whittaker.MirabolicPairingStatement`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.

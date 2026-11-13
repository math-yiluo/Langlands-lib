# All-field port of `Langlands.Representation.Whittaker.MirabolicCompactTwistedPairingProof`

`Langlands.AllField.Representation.Whittaker.MirabolicCompactTwistedPairingProof` is the all-field port of the Library module `Langlands.Representation.Whittaker.MirabolicCompactTwistedPairingProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Whittaker.MirabolicCompactTwistedPairingProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**The normalized absolute value is one on an open subgroup of units**

The one field-specific lemma of the p-adic module
`Langlands.Representation.Whittaker.MirabolicCompactTwistedPairingProof` that the
unequal-rank functional equation needs. For supplied data `T : LocalFieldData F`, the
normalized absolute value is one on an open subgroup of `Fˣ`. The field-generic
declarations of that module are used from the original, which this module imports. Its
main theorem, the one-dimensionality of the compact mirabolic twisted pairing, is not
ported.

## Imports from the port

- `Langlands.AllField.Group.GL.BlockModulus`
- `Langlands.AllField.Group.GL.CompactOpen`
- `Langlands.AllField.Group.GL.UnramifiedCharacter`
- `Langlands.AllField.Representation.Whittaker.MirabolicPairingStatement`

## Declarations

- `Langlands.AllField.Whittaker.MirabolicCompactTwistedPairing.isOpenNormOne_normalizedAbsoluteValue` (theorem): The normalized absolute value of supplied local-field data `T` is one on an open
  subgroup of units.

Public declarations of the original that are not re-declared here: `Langlands.Whittaker.MirabolicCompactTwistedPairing.nonempty_linearEquiv_complex`, `Langlands.Whittaker.MirabolicCompactTwistedPairing.isSmooth_characterRepresentation`, `Langlands.Whittaker.MirabolicCompactTwistedPairing.mirabolicCharacter_scale_neg_one_mul`, `Langlands.Whittaker.MirabolicCompactTwistedPairing.nonempty_oppositeForms_equiv`, `Langlands.Whittaker.MirabolicCompactTwistedPairing.valuative_nonarchimedean`, `Langlands.Whittaker.mirabolicCompactTwistedPairing`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.

# All-field port of `Langlands.Representation.RankinSelberg.UnequalRankMirabolicPairingStatement`

`Langlands.AllField.Representation.RankinSelberg.UnequalRankMirabolicPairingStatement` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.UnequalRankMirabolicPairingStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.UnequalRankMirabolicPairingStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Irreducible unequal-rank mirabolic pairings**

The two conclusions of the Lemma in JPSS (1983), Section 2.11, printed
p.399, stated for the published actual covariance space. The parameter `s`
is the integral parameter; the source's twisted-pairing parameter is
`s - (r-n)/2`. These are proposition targets, with no proof or extension
to the full Whittaker-type uniqueness target.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.UnequalRankBilinearUniquenessStatement`

## Declarations

- `Langlands.AllField.RankinSelberg.UnequalRankMirabolicPairingRigidityStatement` (def): Outside a finite set of spectral values `q^(-s)`, a nonzero covariant
  pairing between a smooth irreducible mirabolic representation and an
  admissible irreducible smaller general linear representation forces the
  compact standard model and an inverse-standard Whittaker functional.
- `Langlands.AllField.RankinSelberg.UnequalRankCompactGenericPairingStatement` (def): For the actual compact mirabolic model and an admissible irreducible
  smaller representation with an inverse-standard Whittaker functional,
  the covariant pairing space is linearly equivalent to `ℂ` for every `s`.

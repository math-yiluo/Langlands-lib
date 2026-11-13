# All-field port of `Langlands.Representation.RankinSelberg.UnequalRankCompactPairingFunctionals`

`Langlands.AllField.Representation.RankinSelberg.UnequalRankCompactPairingFunctionals` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.UnequalRankCompactPairingFunctionals`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Source: the original module `Langlands.Representation.RankinSelberg.UnequalRankCompactPairingFunctionals` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Unequal-rank compact pairings and inverse-standard Whittaker functionals**

For `n < r`, the unequal-rank covariant forms on the compact mirabolic model of rank
`r + 1` against a smooth representation `η` of `GL_(n+1)` embed linearly into the
inverse-standard Whittaker functionals of `η`, and there is a nonzero form as soon as `η`
has a nonzero such functional. The proof reduces `r` to `n + 1` by restriction along the
successor embedding and identifies the adjacent-rank forms with invariant forms on
`c-Ind_N^(GL_(n+1)) θ × η`. Consequently the form space is a line whenever the
inverse-standard Whittaker functionals of `η` form a line.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.UnequalRankMirabolicPairingStatement`
- `Langlands.AllField.Representation.Whittaker.MirabolicCompactTwistedPairingProof`

## Declarations

- `Langlands.AllField.RankinSelberg.UnequalRankCompactPairing.nonempty_equiv_complex_padic` (theorem): For a nonarchimedean local field with the topology of the supplied data `T`, the
  unequal-rank forms on the actual compact mirabolic model against a smooth
  representation `η` with a nonzero inverse-standard Whittaker functional form a line,
  provided the inverse-standard Whittaker functionals of `η` form a line.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.UnequalRankCompactPairing.exists_injective_of_forall_eq_smul`, `Langlands.RankinSelberg.UnequalRankCompactPairing.inverseStandardCharacter_mul`, `Langlands.RankinSelberg.UnequalRankCompactPairing.exists_injective_adjacent`, `Langlands.RankinSelberg.UnequalRankCompactPairing.exists_ne_zero_adjacent`, `Langlands.RankinSelberg.UnequalRankCompactPairing.exists_injective`, `Langlands.RankinSelberg.UnequalRankCompactPairing.exists_ne_zero`, `Langlands.RankinSelberg.UnequalRankCompactPairing.nonempty_equiv_complex`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.

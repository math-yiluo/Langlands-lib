# All-field port of `Langlands.Representation.RankinSelberg.UnequalRankMirabolicPairingProof`

`Langlands.AllField.Representation.RankinSelberg.UnequalRankMirabolicPairingProof` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.UnequalRankMirabolicPairingProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.UnequalRankMirabolicPairingProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Proof of irreducible unequal-rank mirabolic pairing rigidity**

This module proves `UnequalRankMirabolicPairingRigidityStatement` (JPSS 1983,
Section 2.11, Lemma on printed p.399). The proof is by induction on the rank `r > n`.
The step applies the unnormalized `Φ⁻` to the mirabolic representation, which
shifts the parameter by `1/2`. In the adjacent case `r = n + 1` there are two
cases. A radical-trivial representation admits a nonzero form only at finitely
many spectral values, by the Schur scalars of the center. A radical-generated
representation is reduced by the mixed transfer to a form between `Φ⁻ ξ` and
`η|_(P_n)`. The tower claim `C(n)` then handles that form.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.FunctionalEquationStatement`
- `Langlands.AllField.Representation.RankinSelberg.UnequalRankMirabolicMixedTransfer`
- `Langlands.AllField.Representation.RankinSelberg.UnequalRankMirabolicPairingStatement`
- `Langlands.AllField.Representation.RankinSelberg.UnequalRankMirabolicTowerClaim`

## Declarations

- `Langlands.AllField.RankinSelberg.UnequalRankRigidity.exists_descent_ne_zero` (theorem): First-variable descent: a nonzero covariant form of rank `m + 1` at `s`
  descends through the `θ_ψ`-coinvariants of the radical to a nonzero covariant form
  of rank `m` at `s - 1/2` on the unnormalized `Φ⁻ ξ`.
- `Langlands.AllField.RankinSelberg.UnequalRankRigidity.rigidity_adjacent` (theorem): The adjacent case `r = n + 1`, with a standard Whittaker functional.
- `Langlands.AllField.RankinSelberg.UnequalRankRigidity.rigidity_of_lt` (theorem): All ranks `r > n`, with a standard Whittaker functional, by induction on `r`.
- `Langlands.AllField.RankinSelberg.unequalRankMirabolicPairingRigidity` (theorem): JPSS (1983), Section 2.11, Lemma (printed p.399), for the actual compact and
  covariance models: outside finitely many spectral values, a nonzero covariant
  pairing forces the compact mirabolic model and an inverse-standard Whittaker
  functional.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.UnequalRankRigidity.unequalRankEmbedding_adjacent`, `Langlands.RankinSelberg.UnequalRankRigidity.det_scalar`, `Langlands.RankinSelberg.UnequalRankRigidity.determinantWeight_scalar`, `Langlands.RankinSelberg.UnequalRankRigidity.spectralPoint_sub`, `Langlands.RankinSelberg.UnequalRankRigidity.spectralPoint_sub_notMem`, `Langlands.RankinSelberg.UnequalRankRigidity.hasFunctional_inverse_of_standard`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.

# All-field port of `Langlands.Representation.RankinSelberg.UnequalRankMirabolicMixedTransfer`

`Langlands.AllField.Representation.RankinSelberg.UnequalRankMirabolicMixedTransfer` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.UnequalRankMirabolicMixedTransfer`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.UnequalRankMirabolicMixedTransfer` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Mixed transfer through unnormalized `Φ⁻`**

Let `ξ` be a smooth radical-generated representation of `P_(n+1)` and `η` a smooth
representation of `GL_(n+1)`. A nonzero bilinear form `β` with
`β(ξ(levi g) v, η(g) w) = |det g|^(-s) β(v, w)` is integrated against `θ_ψ⁻¹` along
the radical. The result descends to the unnormalized `Φ⁻ ξ` and is a nonzero form on
`Φ⁻ ξ` and `η|_(P_n)` with covariance `|det h|^(-(s - 1))`. The argument adapts the
published proof of `Derivative.Mirabolic.phiMinusPairingTransfer` to a second
representation of `GL_(n+1)`.

## Imports from the port

- `Langlands.AllField.Representation.Derivative.MirabolicMinusPairingTransferProof`
- `Langlands.AllField.Representation.Smooth.SmallRealizationProof`
- `Langlands.AllField.Representation.Whittaker.MirabolicPairingStatement`

## Declarations

- `Langlands.AllField.RankinSelberg.UnequalRankMixedTransfer.exists_open_subgroup_coefficient_mixed` (theorem): An open subgroup of `GL_(m+1)` under which the radical coefficient of `x` and `w`
  is invariant.
- `Langlands.AllField.RankinSelberg.UnequalRankMixedTransfer.exists_coefficient_support_mixed` (theorem): Radical coefficients of a radical-generated representation have compact support.
- `Langlands.AllField.RankinSelberg.UnequalRankMixedTransfer.mixedTransfer` (theorem): Mixed transfer: a nonzero form between a smooth radical-generated representation `ξ`
  of `P_(n+1)` and a smooth representation `η` of `GL_(n+1)`, covariant under the Levi
  `GL_(n+1)` with weight `|det g|^(-s)`, gives a nonzero form between the unnormalized
  `Φ⁻ ξ` and `η|_(P_n)` with weight `|det h|^(-(s - 1))`.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.UnequalRankMixedTransfer.transferIntegral_levi_mixed`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.

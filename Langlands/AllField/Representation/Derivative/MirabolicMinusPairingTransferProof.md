# All-field port of `Langlands.Representation.Derivative.MirabolicMinusPairingTransferProof`

`Langlands.AllField.Representation.Derivative.MirabolicMinusPairingTransferProof` is the all-field port of the Library module `Langlands.Representation.Derivative.MirabolicMinusPairingTransferProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Derivative.MirabolicMinusPairingTransferProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Proof of the pairing transfer through unnormalized `Φ⁻`**

A covariant pairing `β` of `ξ` and `ξ'` is integrated against `θ_ψ⁻¹` along the radical:
`β̃(v, w) = ∫ ψ(-c_last) β(ξ(u c) v, ξ'(ε) w) dc`, with `ε = levi (-1)`. The integrand is
locally constant and compactly supported, `β̃` descends to the `θ_ψ`-coinvariants, and a
Haar change of variables gives covariance `|det|^(1 - s)` on the smaller mirabolic group.
A finite character sum shows that some Levi translate of `β̃` is nonzero. See the paired
Markdown for the route.

## Imports from the port

- `Langlands.AllField.HarmonicAnalysis.PadicRectangularHaarScalingProof`
- `Langlands.AllField.Representation.Derivative.MirabolicLatticeBox`
- `Langlands.AllField.Representation.Derivative.MirabolicMinusPairingTransferStatement`

## Declarations

- `Langlands.AllField.Derivative.Mirabolic.exists_integral_character_ne_zero` (theorem): A locally constant, compactly supported function `f` on `F^(k+1)` with `f 0 ≠ 0` has
  a nonzero twisted integral `∫ ψ(-(y ⬝ c)) f(c) dc` at some `y ≠ 0`.
- `Langlands.AllField.Derivative.Mirabolic.exists_latticeBox_fixes` (theorem): A smooth vector is fixed by the radical elements of some lattice box.
- `Langlands.AllField.Derivative.Mirabolic.exists_mulVec_eq_add` (theorem): Near the identity, `GL_(m+1)` moves every large vector `c` to `c + d`.
- `Langlands.AllField.Derivative.Mirabolic.exists_open_subgroup_coefficient` (theorem): An open subgroup of `GL_(m+1)` under which the radical coefficient of `x` and `w`
  is invariant.
- `Langlands.AllField.Derivative.Mirabolic.exists_coefficient_support` (theorem): Radical coefficients of a radical-generated representation have compact support.
- `Langlands.AllField.Derivative.Mirabolic.phiMinusPairingTransfer` (theorem): Unnormalized `Φ⁻` transfers nonzero covariant pairings of radical-generated smooth
  representations, lowering the exponent by one.

Public declarations of the original that are not re-declared here: `Langlands.Derivative.Mirabolic.rep_radicalElement_mul`, `Langlands.Derivative.Mirabolic.rep_radicalElement_zero`, `Langlands.Derivative.Mirabolic.levi_neg_one_mul_radicalElement`, `Langlands.Derivative.Mirabolic.levi_neg_one_commute`, `Langlands.Derivative.Mirabolic.determinantWeight_levi`, `Langlands.Derivative.Mirabolic.determinantWeight_radicalElement`, `Langlands.Derivative.Mirabolic.transferIntegral`, `Langlands.Derivative.Mirabolic.integrable_transferIntegrand`, `Langlands.Derivative.Mirabolic.transferForm`, `Langlands.Derivative.Mirabolic.transferForm_apply`, `Langlands.Derivative.Mirabolic.transferIntegral_radical_left`, `Langlands.Derivative.Mirabolic.transferIntegral_radical_right`, `Langlands.Derivative.Mirabolic.transferIntegral_levi`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.

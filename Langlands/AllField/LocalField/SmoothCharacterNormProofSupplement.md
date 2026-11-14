# All-field supplement to `Langlands.AllField.LocalField.SmoothCharacterNormProof`

`Langlands.AllField.LocalField.SmoothCharacterNormProofSupplement` supplements the Library module `Langlands.AllField.LocalField.SmoothCharacterNormProof`, the existing all-field port of `Langlands.LocalField.SmoothCharacterNormProof`. The original belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The module imports the original, so the field-independent declarations of the original are available to it unchanged. This module re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use and that `Langlands.AllField.LocalField.SmoothCharacterNormProof` does not already provide. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.LocalField.SmoothCharacterNormProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Proof of the real norm decomposition of a smooth scalar character**

A character of `F^×` with open kernel has absolute value one on the norm-one
units, because these units form a compact group in which the kernel is an open
subgroup of finite index. Every unit is a norm-one unit times an integer power of
the specified uniformizer, so the absolute value of the character is
`‖ω ϖ‖ ^ ord a`, which is `|a| ^ c` for `c = -log_q ‖ω ϖ‖`. The exponent is
unique because `0 < |ϖ| = q⁻¹ < 1`.

## Imports from the port

- `Langlands.AllField.LocalField.SmoothCharacterNormProof`
- `Langlands.AllField.LocalField.SmoothCharacterNormStatement`

## Declarations

- `Langlands.LocalFieldData.norm_eq_one_of_normalizedAbs_eq_one` (theorem): A character with open kernel has complex norm one at every unit of
  residue-normalized absolute value one.
- `Langlands.LocalFieldData.norm_eq_norm_uniformizer_zpow_ord` (theorem): A character with open kernel has complex norm `‖ω ϖ‖ ^ ord a` at a unit `a`.
- `Langlands.LocalFieldData.smoothCharacterNormDecomposition` (theorem): Proof of `SmoothCharacterNormDecomposition`: the exponent is
  `-log_q ‖ω ϖ‖`, and it is unique since `0 < |ϖ| < 1`.

Declarations of the original re-declared by `Langlands.AllField.LocalField.SmoothCharacterNormProof` and therefore not here: `Langlands.PadicField.TopologicalData.normalizedAbs_eq_one_iff_valuation_eq_one`, `Langlands.PadicField.TopologicalData.isCompact_normalizedAbs_eq_one_units`.

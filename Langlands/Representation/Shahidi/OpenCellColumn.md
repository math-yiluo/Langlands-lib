# Integrals over columns

Module `Langlands.Representation.Shahidi.OpenCellColumn`, namespace
`Langlands.Shahidi.OpenCell`.

## Contents

- `columnSplit`, `joinColumn`, `measurePreserving_columnSplit`, `integral_column`: Fubini for an
  integrable function of a column of length `n + 1` split into its last entry and the rest.
- `integral_inv_smul`, `integral_neg`: the change of variables `X ↦ c⁻¹ X` multiplies by
  `|c|^(a b)`; `X ↦ -X` preserves the integral.
- `latticeSet ϖ k = ϖ^(-k) 𝒪` (increasing in `k` when `|ϖ| ≤ 1`) and the integrals of `conj ψ`
  over it: `1` for `k = 0` (`integral_conj_char_zero`) and `0` for `k ≥ 1`
  (`integral_conj_char_eq_zero`) when `ψ` has conductor `𝒪`.
- `integral_outer`: let `ψ` have conductor `𝒪` and let `C : ℕ → ℂ` vanish beyond some bound
  (`C(e) = 0` for `e > D`). A function that equals `C(0)` on `𝒪` and `conj ψ(c) C(e)` at every
  `c` with `|c| = q^e`, `e ≥ 1`, has integral `C(0) - C(1)` (the vanishing of `C` makes the
  function supported on the compact set `ϖ^(-D) 𝒪`).

## Provenance

Standard computations with the Haar measure of `Langlands.Representation.Shahidi.OpenCellHaar`.

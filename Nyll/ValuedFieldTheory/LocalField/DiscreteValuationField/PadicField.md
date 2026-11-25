# The p-adic field ℚ_p as a local field

Module `Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PadicField`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

This file treats ℚ_p as the basic example of the library's local fields. It equips ℚ_p with the valuation coming from the discrete valuation ring ℤ_p, checks completeness and the residue field, and specializes general results on the logarithm and exponential series and on roots of unity to ℚ_p. Statements use Mathlib's `ℚ_[p]`, `ℤ_[p]` and `Padic.mulValuation` directly.

## The local-field structure

- `padicDVRValuation p`: the valuation on ℚ_p with values in `ℤᵐ⁰` attached to the maximal ideal of ℤ_p. Its valuation subring is identified with ℤ_p (`padicIntEquivValuationSubring`), it is rank one and discrete (an instance), and `padicDVRValuation_apply_p` computes the value of `p` as `exp (-1)`, so `p` is a uniformizer (`padicDVRValuation_isUniformizer_p`).
- `padicDVRValuation_isAdicComplete`: the valuation subring is complete for its maximal-ideal-adic topology, transported from the adic completeness of ℤ_p; this gives the instance `IsCompleteDiscrete`.
- `padicCompleteDVF p`: the resulting complete discretely valued field structure on ℚ_p. Its residue field is finite and has exactly `p` elements (`padicCompleteDVF_residueField_finite`, `padicCompleteDVF_residueField_card`), using the residue field `ZMod p` of ℤ_p.
- `padicLocalField p`: ℚ_p as a `LocalField`, i.e. this complete structure together with finiteness of the residue field.

## Series and roots of unity

- `padicMulValuationNhds p x`: the neighbourhood filter of `x` for the topology defined by `Padic.mulValuation`.
- `tendsto_zero_logSeriesTermField_padic_mulValuation_of_lt_one` and its signed form: if `Padic.mulValuation x < 1`, the terms of the logarithm series tend to 0. `tendsto_zero_expSeriesTermField_padic_mulValuation_of_lt_exp_neg_one`: if `Padic.mulValuation x < exp (-1)`, the terms of the exponential series tend to 0. Both specialize general estimates of the library, fed with the valuations of `n + 1` and of `n!` computed here.
- Membership in `rootsOfUnity (p^m) ℚ_[p]` is the equation `ζ^(p^m) = 1`, and a primitive `p^m`-th root of unity in ℚ_p is a root of the cyclotomic polynomial of order `p^m`.

## Watch for

- `CompleteDVF` and `LocalField` are the library's own structures carrying a chosen valuation, not Mathlib's local-field classes; this file does not compare `padicDVRValuation p` with Mathlib's valuation on ℚ_p.
- The convergence statements are for the topology of `Padic.mulValuation`, through `padicMulValuationNhds`, not for the metric topology of the `ℚ_[p]` instance; the file does not compare the two.
- The exponential estimate uses the radius `v(x) < exp (-1)`, i.e. p-adic order at least 2, for every `p`; this is smaller than the usual radius of convergence when `p` is odd.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/PadicField.lean`: the Lean file is the source byte for byte (SHA-256 `cc37e060fb7cc164d92e15c109ae4e2f7d1c21d9f78b14ece077ea2c03382a3b`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.

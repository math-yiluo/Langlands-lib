# Exponential and logarithm between 𝔪ⁿ and Uⁿ

Module `Nyll.ValuedFieldTheory.LocalField.Analytic.PrincipalUnitExpLogEquiv`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a complete discretely valued field of characteristic zero with finite residue field, the file packages the exponential and logarithm series as mutually inverse isomorphisms of topological groups between the n-th power of the maximal ideal and the n-th higher principal unit group, for n > e/(p − 1).

## Main definition

`chosenExpLogContinuousMulEquiv v hv n hlevel` is a `≃ₜ*` from `Multiplicative (𝔪 ^ n)` (the additive group 𝔪ⁿ written multiplicatively) to `higherPrincipalUnitGroup F n`, where `F = completeDVFOfWithZeroValuation v`. Hypotheses: `v : Valuation K ℤᵐ⁰` with an instance `IsCompleteDiscrete v`, a finite residue field, `CharZero K`, `v` surjective, and e/(p − 1) < n, with e the ramification index and p the residue characteristic attached to `v` by `LocalField.ofWithZeroValuation`.

The construction fixes a uniformizer π with v(π) = exp(−1), derives from the local-field structure the values v(m + 1) and v(m!) as exp(−e·v_p(·)), and the completeness of the topology of `v`. It then takes the exponential map 𝔪ⁿ → Uⁿ and the logarithm map Uⁿ → 𝔪ⁿ of the imported files, checks the two composites are the identity using the evaluated composition identities `logOnePlusSeries_expSeries_sub_one_eq_self_ofWithZeroValuation_scaled_of_threshold` and `expSeries_logOnePlusSeries_eq_one_add_ofWithZeroValuation_scaled_of_threshold`, and assembles the equivalence with `principalUnitExpLogContinuousMulEquivOfExact_ofWithZeroValuationScaled`.

## Watch for

- This is a `def` (data), and the uniformizer is chosen by `Classical.choose`, hence the name.
- Surjectivity of `v` is the normalization: the valuation must take the value exp(−1).

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/Analytic/PrincipalUnitExpLogEquiv.lean`: the Lean file is the source byte for byte (SHA-256 `8f25278ceb4e91150a721c4c50090395e3c9b282aae87222660a02f20eaf9e7d`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.

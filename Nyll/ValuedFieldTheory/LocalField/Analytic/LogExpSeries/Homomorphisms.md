# The principal-unit logarithm as a homomorphism, conditional on additivity

Module `Nyll.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.Homomorphisms`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a complete discretely valued field `K` with valuation `v : Valuation K ℤᵐ⁰`, the file studies the logarithm series Log on the first principal units U¹: its valuation above the threshold 1/(p − 1), its interplay with the exponential, and the reduction of Log(uw) = Log u + Log w to the convergence of a "defect" sequence. Assuming that convergence, it packages Log as a homomorphism on U¹ and extends it to Kˣ through a decomposition of Kˣ into roots of unity, U¹ and powers of a uniformizer.

## Results on U¹

Throughout, `p` is a prime, `hnval` says v(n+1) = exp(−v_p(n+1)) for all n, and `hcomplete` says `K` is complete for `Valued.mk' v`.

- `principalUnitLogSeries_valuation_eq_subOne_of_inv_sub_one_lt`: if the integer valuation of u − 1 exceeds 1/(p − 1), then v(Log u) = v(u − 1). Hence `principalUnitLogSeries_eq_zero_iff_eq_one_of_inv_sub_one_lt`: on that domain, Log u = 0 iff u = 1.
- For x with v x < exp(−1) and integer valuation above 1/(p − 1), Log(Exp x) has the valuation of x and vanishes only for x = 0; on the threshold domain, if also v(Log u) < exp(−1) (hypothesis `hvlogExp`), Exp(Log u) = 1 iff u = 1.
- `hasSum_principalUnitLogSeries_ofWithZeroValuation` and product forms: Log(uw) is the log series at (u−1) + (w−1) + (u−1)(w−1); partial sums (`principalUnitLogPartialSumOfWithZeroValuation`) converge.

## Additivity and homomorphisms

- `principalUnitLogSeries_mul_eq_add_of_tendsto_field_defect_ofWithZeroValuation`: Log(uw) = Log u + Log w, given `hdefect` (limits compared by `eq_of_tendsto_sub_zero`).
- `principalUnitLogSeriesHomOfTendstoFieldDefect_ofWithZeroValuation`: Log as U¹ →* `Multiplicative K`, given `hdefect` for all u, w.
- `fieldUnitLogHomOfPrincipalUnitHom`: for an equivalence `e` from `fieldUnitDecompositionFactors F` to Kˣ and any φ : U¹ →* `Multiplicative A`, the homomorphism on Kˣ that is φ on the U¹ factor and trivial on the other two.
- `fieldUnitLogSeriesHomOfTendstoFieldDefect_ofWithZeroValuationUniformizer`: the resulting logarithm Kˣ →* `Multiplicative K` for the decomposition built from a uniformizer π; it agrees with Log on U¹ and kills Teichmüller roots and π.

## Watch for

- Additivity and every homomorphism built from the Log series take the hypothesis `hdefect`: the log partial sums at (u−1) + (w−1) + (u−1)(w−1), minus those at u − 1 and at w − 1, tend to 0. It stands for the functional equation of the logarithm, which is not proved here; the comments call it the remaining analytic step.
- `hnval` has no ramification factor: it forces v(p) = exp(−1), and the threshold is 1/(p − 1).
- The logarithm on Kˣ requires a finite residue field, depends on the chosen decomposition and kills the chosen uniformizer. Values lie in `Multiplicative K`, where multiplication is addition in `K`.
- `hcomplete` is assumed separately from the instance `IsCompleteDiscrete v`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/Analytic/LogExpSeries/Homomorphisms.lean`: the Lean file is the source byte for byte (SHA-256 `817b1a4eaffc651a86b0d240a96849661d44fd8e4b0e646829be11f5a40c686c`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.

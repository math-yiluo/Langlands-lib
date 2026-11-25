# The p-adic Lubin–Tate series over the completed unramified Witt ring

Module `Nyll.ClassFieldTheory.LubinTate.Padic.ChangedUniformizerIntertwiner.CompletedSeries`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Over ℚ_p, two Lubin–Tate series are compared in the changed-uniformizer construction: the multiplicative series (1 + X)^p − 1 for the uniformizer p, and the standard series for the changed uniformizer u·p, where u is a unit of ℤ_p. The file maps both into power series over W(k), the Witt ring of an algebraic closure k of ℤ/p, and records their coefficients and their reductions modulo p.

## Main definitions

- `padicCompletedMultiplicativeSeries p`: the multiplicative Lubin–Tate series with coefficients mapped into W(k).
- `padicCompletedChangedStandardSeries p u`: the standard series for u·p with coefficients mapped into W(k).

## Main results

- `padicCompletedMultiplicativeSeries_eq`: the first series is (1 + X)^p − 1.
- `padicCompletedChangedStandardSeries_eq`: the second is (u·p)·X + X^p.
- `padicCompletedMultiplicativeSeries_constantCoeff`, `padicCompletedMultiplicativeSeries_coeff_one`, `padicCompletedChangedStandardSeries_constantCoeff`: zero constant coefficients, and linear coefficient p for the first.
- `padicCompletedMultiplicativeSeries_hasSubst`, `padicCompletedChangedStandardSeries_hasSubst`: both can be substituted into power series.
- `padicCompletedMultiplicativeSeries_map_constantCoeff`, `padicCompletedChangedStandardSeries_map_constantCoeff`: reducing coefficients to k by the zeroth Witt coordinate gives X^p in both cases.
- `padicChangedUniformizerFrobenius_constantCoeff_eq_zero`: applying Witt Frobenius to the coefficients of a series with zero constant term keeps it zero.

## Proofs

The formulas unfold the definitions, using that the residue field of ℚ_p has p elements and that p maps to p in W(k). The reductions use the Frobenius identity (1 + X)^p = 1 + X^p in characteristic p and the vanishing of p in k.

## Watch for

- The setting is ℚ_p only, through the library's `padicLocalField p`; W(k) stands in for the ring of integers of the completed maximal unramified extension.
- The series here are plain power series over W(k), not `LubinTateSeries` structures, since that structure is defined over the valuation ring of a `LocalField`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LubinTate/Padic/ChangedUniformizerIntertwiner/CompletedSeries.lean`: the Lean file is the source byte for byte (SHA-256 `a8b4cf77334c0d9bc05f743231eeb63eb57ed45adc525b37e374aae4e955e929`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.

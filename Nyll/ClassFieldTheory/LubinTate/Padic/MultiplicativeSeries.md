# The multiplicative Lubin–Tate series over ℚ_p

Module `Nyll.ClassFieldTheory.LubinTate.Padic.MultiplicativeSeries`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

This file makes (1 + X)ᵖ − 1 a Lubin–Tate series over ℚ_p for the uniformizer `p`, in the sense of the library's structure `LubinTateSeries`.

- `padicMultiplicativeLubinTateSeries p`: the series, taken as Mathlib's binomial series `PowerSeries.binomialSeries` at exponent `p` minus 1. The file checks the three conditions of the structure: zero constant term, linear coefficient `p`, and reduction Xᵖ modulo the maximal ideal (Xᵠ with q the size of the residue field, here `p`).
- `LubinTateSeries.padicMultiplicativeLubinTateSeries_toPowerSeries`: the underlying series is literally the binomial series minus 1 (a simp lemma).
- `padicMultiplicativeLubinTateSeries_isUniformizer`: `p` is a uniformizer for the valuation of `padicLocalField p`.

The reduction condition uses that the residue field of ℚ_p is 𝔽_p, of characteristic `p`, so that (1 + X)ᵖ = 1 + Xᵖ there.

The underlying power series is a binomial series minus 1, not a polynomial; lemmas elsewhere rewrite it as (1 + X)ᵖ − 1.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LubinTate/Padic/MultiplicativeSeries.lean`: the Lean file is the source byte for byte (SHA-256 `992f235b17814f8499afbb21df5540c460cbc4ef51af63aa7b0f9444c98c9957`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.

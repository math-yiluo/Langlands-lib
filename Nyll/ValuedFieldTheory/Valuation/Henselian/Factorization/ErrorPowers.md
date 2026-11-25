# The power step of Hensel's iteration

Module `Nyll.ValuedFieldTheory.Valuation.Henselian.Factorization.ErrorPowers`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

This file carries out the step from precision π^n to precision π^(n+1) in the coefficientwise proof of Hensel's lemma, over an arbitrary commutative ring `R`. Given an approximate factorization f − g·h = π^n·f_n and a correction pair (p, q) with g·q + h·p ≡ f_n modulo π, the update g ↦ g + π^n·p, h ↦ h + π^n·q leaves an error divisible by π^(n+1).

## Main results

- `henselFactorization_power_update_error_coeff_mem_span_singleton`: for n ≥ 1, if f − g·h = C(π^n)·f_n and every coefficient of g·q + h·p − f_n lies in (π), then every coefficient of f − (g + C(π^n)·p)(h + C(π^n)·q) lies in (π^(n+1)).
- `henselFactorization_power_update_error_factor_exists`: the same statement in factor form: the new error is C(π^(n+1))·f_(n+1) for some polynomial f_(n+1).
- `henselFactorization_power_update_error_factor_exists_of_maximalIdeal_correction_le`: the local-ring form, where the correction congruence is given modulo the maximal ideal m, and m ≤ (π) is assumed so that it can be read modulo (π).

Helper lemmas turn coefficientwise membership in (a) into a factor C(a)·Q, show conversely that a displayed factor C(π^n)·Q puts every coefficient in (π^n), in (π)^n and, in a local ring with π ∈ m, in m^n, and record that π^n·x ∈ (π^(n+1)) when x ∈ (π).

## Proof

The new error is expanded as π^n·(f_n − (g·q + h·p)) − π^(2n)·p·q. The first term lies in (π^(n+1)) by the correction congruence, the second because n ≥ 1. Coefficientwise divisibility is turned into a factor with Mathlib's `Polynomial.C_dvd_iff_dvd_coeff`.

## Points to watch

- The hypothesis n ≥ 1 is essential: it is what absorbs the quadratic term π^(2n)·p·q.
- The local-ring form assumes m ≤ (π), not π ∈ m; no valuation and no completeness enter this file.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/Henselian/Factorization/ErrorPowers.lean`: the Lean file is the source byte for byte (SHA-256 `a5b03ab54e031a9559aacda07d620a58f8dbefe551ba559eb96d3a3a0d655969`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.

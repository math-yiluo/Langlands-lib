# Coefficient maxima and the reduction of a normalized polynomial

Module `Nyll.ValuedFieldTheory.Valuation.Henselian.IrreduciblePolynomialBounds`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

This file prepares the residue-field input for the coefficient estimate on irreducible polynomials (for irreducible f = a_0 + … + a_n X^n, every |a_i| is at most max(|a_0|, |a_n|)), which is proved elsewhere with Hensel's lemma. Here `K` is a field with a real-valued absolute value v that is nonarchimedean in the library's sense (`LubinTate.Valuations.NonarchimedeanAbsoluteValue`), and O = `absoluteValueValuationSubring v hnonarch` is its closed unit ball, a valuation ring with residue field k. The file shows that if both endpoint coefficients are strictly below the maximum, the reduction of the normalized polynomial splits into two coprime factors, the situation to which Hensel's lemma applies.

## Definition

- `polynomialCoeffAbsMax v f`: the maximum of |a_i| over i ≤ deg f. The results below take the maximum as an explicit real number instead.

## Main results

For F ∈ O[X] with reduction F̄ ∈ k[X]:

- Coefficients with |F_i| < 1 reduce to 0, those with |F_i| = 1 to nonzero elements.
- If some coefficient has absolute value 1, the first such index r satisfies X^r ∣ F̄ but not X^(r+1) ∣ F̄, and the last such index s is the degree of F̄. If |F_0| < 1 and |lc F| < 1, then 0 < r ≤ s < deg F (`irreduciblePolynomial_exists_first_last_abs_eq_one_coeff`).
- `irreduciblePolynomial_exists_hensel_reduction_factor_input`: under |F_0| < 1, |lc F| < 1 and some |F_n| = 1, there is r with 0 < r < deg F such that F̄ = X^r · (F̄ /ₘ X^r), the quotient has nonzero constant term, and X^r and the quotient are coprime.
- `irreduciblePolynomial_exists_hensel_reduction_factor_input_of_field_coeffs`: the same for f ∈ K[X] with all |a_i| ≤ 1, |a_0| < 1, |a_n| < 1 and some coefficient of absolute value 1, after lifting f to F ∈ O[X] of the same degree.
- Normalization: a nonzero f attains a positive maximum M of its coefficient absolute values at some index j ≤ deg f (`irreduciblePolynomial_exists_coeff_abs_max_of_ne_zero`); g = a_j⁻¹·f has the same degree, all coefficients in O and |g_j| = 1; if |a_0| < M and |lc f| < M, then g has constant and leading coefficients of absolute value below 1. `irreduciblePolynomial_normalized_scale_hensel_reduction_factor_input` combines this with the previous item.

## Proof

The first and last indices are chosen with `Nat.find` and a finite maximum; coprimality holds because the quotient is not divisible by the prime X.

## Points to watch

- Despite the `irreduciblePolynomial_` prefix, no statement here assumes irreducibility or applies Hensel's lemma; the file supplies only the reduction data.
- The absolute value is real-valued, so this concerns valuations of rank at most one; the maximum and scaling lemmas need no nonarchimedean hypothesis.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/Henselian/IrreduciblePolynomialBounds.lean`: the Lean file is the source byte for byte (SHA-256 `be0f35f8b1cca23a96dfd57c90c0649538dcbf8b16b2f4fa410d1fe6901cd10a`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.

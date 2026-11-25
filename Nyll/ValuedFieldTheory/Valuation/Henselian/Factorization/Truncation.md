# Degree truncation of the Hensel correction

Module `Nyll.ValuedFieldTheory.Valuation.Henselian.Factorization.Truncation`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

In the correction step of Hensel's lemma, dividing b·f_n by the lift g0 gives b·f_n = g0·q + p, and the provisional second correction Q = a·f_n + h0·q satisfies g0·Q + h0·p ≡ f_n, but its degree is not controlled. This file shows that the coefficients of Q above degree d − m already vanish modulo the maximal ideal 𝔪 (or modulo (π)), so cutting Q off at degree d − m keeps the congruence and gives the needed degree bound.

## Definition

- `henselFactorization_lowPart N P`: the sum of the monomials of P of degree at most N, over any semiring, with lemmas on its coefficients, degree and images under ring maps.

## Main results

- `henselFactorization_correction_after_lowPart_ker`, with versions for an ideal, for (π) and for 𝔪: if the coefficients of g0·Q + h0·p − f_n and those of Q above N lie in ker φ, then `lowPart N Q` has degree at most N and satisfies the same congruence.
- Degree division: deg(g·Q) ≤ d forces deg Q ≤ d − m when g has degree m and is nonzero over a field, or has unit leading coefficient.
- `henselFactorization_high_coeff_mem_maximalIdeal_of_product_congruence_degree` and its (π)-version: if g0·Q ≡ A with A of degree at most d after reduction, and g0 reduces to a nonzero polynomial of degree m (resp. has unit leading coefficient and degree m modulo π), then the coefficients of Q above d − m lie in 𝔪 (resp. in (π)).
- `henselFactorization_correction_after_division_degree_truncation`: assume a·g0 + b·h0 ≡ 1 modulo 𝔪, b·f_n = g0·q + p, residual degrees deg f_n ≤ d, deg h0 ≤ d − m, deg p ≤ m, m ≤ d, and g0 reducing to a nonzero polynomial of degree m. Then the truncation Q′ of a·f_n + h0·q at d − m has degree at most d − m and g0·Q′ + h0·p ≡ f_n modulo 𝔪.
- `henselFactorization_correction_after_division_degree_truncation_span_singleton`: the same modulo (π), assuming π ∈ 𝔪, unit leading coefficient and deg g0 = m, a·g0 + b·h0 − 1 = π·e, and the degree bounds before reduction.
- `henselFactorization_correction_congruence_replace_initial_factors` and its (π)-version: a correction congruence for g0, h0 also holds for any g, h congruent to g0, h0.

## Proof

Modulo 𝔪 or (π), the product identity and a degree count bound the degree of the reduction of Q.

## Points to watch

- The (π)-version takes the Bezout relation with an explicit factor π, in place of an assumption that 𝔪 = (π).
- The letter m is a degree, not the maximal ideal.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/Henselian/Factorization/Truncation.lean`: the Lean file is the source byte for byte (SHA-256 `9c990d63ba6909928ec01178564a6e20dfee2a34ea5945b8d72346a1c4f159a9`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.

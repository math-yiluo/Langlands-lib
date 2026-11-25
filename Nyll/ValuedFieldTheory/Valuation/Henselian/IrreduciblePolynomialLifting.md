# Coefficient bound for irreducible polynomials via Hensel's lemma

Module `Nyll.ValuedFieldTheory.Valuation.Henselian.IrreduciblePolynomialLifting`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

This file proves the classical coefficient estimate for irreducible polynomials, assuming the valuation ring is adically complete: if f = a_0 + … + a_n X^n is irreducible, every |a_i| is at most max(|a_0|, |a_n|). Here `K` is a field with a real-valued absolute value v, nonarchimedean in the library's sense (`LubinTate.Valuations.NonarchimedeanAbsoluteValue`), and O = `absoluteValueValuationSubring v hnonarch` is its closed unit ball. The estimate is obtained by contradiction: if |a_0| and |a_n| were both strictly below the maximum of the |a_i|, the reduction data of the coefficient-bounds file and Hensel's lemma would give a nontrivial factorization.

## Main results

- `irreduciblePolynomial_not_irreducible_of_field_factor_natDegree_lt`: a polynomial over a field with a factor g, 0 < deg g < deg f, is not irreducible; `irreduciblePolynomial_not_irreducible_of_valuation_factorization` transports such a factorization from O[X] to K[X].
- `irreduciblePolynomial_hensel_reduction_factor_input_not_irreducible`: if F ∈ O[X] maps to f with the same degree, and F̄ = X^r·Q̄ with 0 < r < deg F, X^r and Q̄ coprime and Q̄(0) ≠ 0, then f is not irreducible. Variants start from f with all |a_i| ≤ 1, |a_0| < 1, |a_n| < 1 and some |a_i| = 1, or from the polynomial normalized by a coefficient of maximal absolute value.
- `irreduciblePolynomial_coeff_abs_le_endpoint_max_of_irreducible`: for irreducible f, |a_i| ≤ max(|a_0|, |a_n|) for every i. The intermediate forms say that a positive coefficient maximum M cannot exceed both endpoint values, so M ≤ max(|a_0|, |a_n|).
- `irreduciblePolynomial_monic_coeff_abs_le_one_of_const_abs_le_one_of_irreducible`: a monic irreducible f with |a_0| ≤ 1 has all coefficients in O; `irreduciblePolynomial_exists_valuation_lift_of_monic_const_abs_le_one_of_irreducible` gives a lift to O[X] of the same degree.

## Proof

The Hensel step uses `henselFactorization_exists_limit_factorization_of_residual_factors_valuationRing` from the assembly file of the factorization development, applied to the coprime residual factors X^r and Q̄; the factor lifting X^r has degree r. Normalizing by a coefficient of maximal absolute value is multiplication by a unit, so it preserves irreducibility.

## Points to watch

- The Hensel obstruction with its variants, the coefficient estimates and the monic consequences assume that O is complete for the topology of its maximal ideal 𝔪, through Mathlib's `IsPrecomplete` and `IsHausdorff`, not completeness of K for v; the two factorization lemmas of the first item and the preservation of irreducibility under scalar normalization do not. For a non-discrete rank-one valuation 𝔪 = 𝔪², so the Hausdorff hypothesis fails; as stated, the results apply in effect to complete discretely valued fields (and trivially valued ones).
- The absolute value is real-valued, so only valuations of rank at most one are covered.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/Henselian/IrreduciblePolynomialLifting.lean`: the Lean file is the source byte for byte (SHA-256 `5993864e68a78251ef013570254284d29c84849b2bda50e93181df24df1255af`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.

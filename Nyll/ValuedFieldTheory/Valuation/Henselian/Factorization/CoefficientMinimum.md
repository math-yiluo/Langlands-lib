# Choosing a coefficient of minimal valuation

Module `Nyll.ValuedFieldTheory.Valuation.Henselian.Factorization.CoefficientMinimum`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

In the approximation proof of Hensel's lemma over a valuation ring one picks, among the finitely many nonzero coefficients of the two initial errors `f − g₀h₀` and `a g₀ + b h₀ − 1`, one of minimal valuation and calls it `π`. The file formalizes this choice as divisibility: in a valuation ring, some element of a finite set divides all the others.

## Definitions and results

- `henselFactorization_exists_mem_finset_dvd_all`: in a `PreValuationRing`, every nonempty finite set contains an element dividing all its elements.
- `henselFactorization_twoPolynomialCoeffFinset P Q`: the finite set of nonzero coefficients of `P` and of `Q`. Its elements are nonzero, and it is empty exactly when `P = Q = 0` (`henselFactorization_twoPolynomialCoeffFinset_empty_iff`).
- `henselFactorization_exists_coeff_dvd_all_two_polynomials`: if this set is nonempty, one of its elements `π` divides every coefficient of `P` and of `Q`. If all coefficients lie in an ideal `I`, then `π ∈ I` and `P = π · P'`, `Q = π · Q'` for some `P'`, `Q'`.
- `henselFactorization_exists_pi_factor_initial_errors_of_residue_lifts_of_nonempty`: over a local valuation ring, if `f̄ = ḡ h̄`, `g₀`, `h₀` lift `ḡ`, `h̄`, and `a g₀ + b h₀` reduces to `1`, then (when the set is nonempty) there is `π` in the maximal ideal with `f − g₀h₀ = π · f₁` and `a g₀ + b h₀ − 1 = π · e₁`. A variant takes the coefficient congruences directly.

## Proofs

The divisibility minimum is an induction on the finite set using that divisibility is total in a valuation ring.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/Henselian/Factorization/CoefficientMinimum.lean`: the Lean file is the source byte for byte (SHA-256 `1ab866c8fa48932a5e9823ae5f9dce1452514cfae2cb6c48b950e9ed3fc22d79`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.

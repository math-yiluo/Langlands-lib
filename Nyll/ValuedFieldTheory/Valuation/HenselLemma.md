# Hensel's lemma for a simple linear factor

Module `Nyll.ValuedFieldTheory.Valuation.HenselLemma`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Over the valuation ring `O` of a Henselian discretely valued field (the library's `HenselianDVF`), the file turns Mathlib's simple-root form of Hensel's lemma into a statement about factorizations: a simple root of the reduction of a monic polynomial `f` lifts to a factorization `f = (X − a) · q` with a coprime cofactor. It also proves uniqueness of simple roots in a residue class.

## Main results

- `eq_of_simple_roots_of_residue_eq` (over any local ring) and `HenselianDVF.eq_of_isRoot_of_isRoot_of_residue_eq_of_derivative_isUnit`: two roots of `f` with the same residue are equal if `f'` is a unit at one of them.
- `exists_linear_factor_lift`, `exists_monic_linear_factor_lift`, `exists_monic_linear_factor_lift_with_monic_quotient`: for `f` monic and `a₀` with `f(a₀) ∈ m` and `f'(a₀)` a unit modulo `m`, there are `a ≡ a₀ mod m` and `q` with `f = (X − a) · q`; the second records that `X − a` is monic, the third also that `q` is monic.
- `exists_monic_linear_factor_lift_of_residue_root` and `exists_monic_linear_factor_lift_of_reduced_simple_root`: the same, starting from a simple root `ā` of the reduction `f̄` in the residue field, with `a` reducing to `ā`.
- `exists_monic_linear_factor_lift_of_reduced_simple_root_with_reduction` adds that `f̄ = (X − ā) · q̄` with `q̄` monic; `..._with_coprime_quotient` adds that `f'(a)` is a unit and that `X − a` and `q` are coprime.
- Helpers: `divByMonic_X_sub_C_eval_eq_derivative_eval` (the quotient of `p` by `X − a`, evaluated at `a`, equals `p'(a)`), `isCoprime_X_sub_C_of_isUnit_eval`, `linearFactor_isCoprime_quotient_of_derivative_isUnit`.

## Proofs

Lifting is `HenselianDVF.exists_lift_root_simple` followed by division by `X − a`. Coprimality comes from a Bézout identity built from the unit `q(a) = f'(a)`. Uniqueness: `q(b)` has the same residue as the unit `q(a)`, so `(b − a) · q(b) = 0` forces `b = a`.

## Caveats

Only a linear factor with a simple residual root is lifted; this is not the general coprime-factorization form of Hensel's lemma.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/HenselLemma.lean`: the Lean file is the source byte for byte (SHA-256 `d9c787e27f9b6c20cac03fa17b6145bfcbe34ae69713f31dba290bacc9b620e2`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.

# Discriminants of monic polynomials over valuation rings

Module `FontaineWintenberger.Mathlib.RingTheory.PolynomialDiscriminant`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

For Mathlib's discriminant `Polynomial.discr` of a monic polynomial `f`, the file proves base change, an integral Bezout identity between `f` and `f′`, the link with separability, and bounds relating the valuation of the discriminant to the derivative at a point and to the distance between two roots.

## Over a commutative ring `R`

- `monic_discr_resultant`: `(−1)^(n(n−1)/2) · disc f` is the resultant of `f` and `f′` taken in degrees `n` and `n − 1`, where `n = deg f`; the case `f = 1` is included.
- `Polynomial.Monic.discr_map`: `disc (f.map φ) = φ (disc f)` for every ring homomorphism `φ`.
- `exists_mul_add_mul_eq_discr`: if `deg f > 0`, there are polynomials `A`, `B` over `R` with `A·f + B·f′ = ± disc f`.
- `monic_derivative_resultant`: padding the degree of `f′` to `n − 1` does not change the resultant.
- `monic_discr_ne_zero_iff`: over a field, `disc f ≠ 0` iff `f` is separable.

Over a domain:

- `exists_monic_two_root_factor`: if `a ≠ b` are roots of `f`, then `f = (X − a)(X − b)·g` with `g` monic.
- `Polynomial.sq_sub_dvd_discr`: then `(a − b)²` divides `disc f`.

## Over the valuation ring of a valued field

Let `v` be a valuation on a field `C` and `f` a monic polynomial over `v.valuationSubring`.

- `monic_root_valuation_le_one`: every root of `f` in `C` has `v ≤ 1`.
- `valuation_discr_le_max`: for `z` in the valuation ring and `deg f > 0`, `v(disc f) ≤ max (v(f(z))) (v(f′(z)))`.
- `valuation_discr_le_derivative`: if moreover `v(f(z)) < v(disc f)`, then `v(disc f) ≤ v(f′(z))`.
- `valuation_discr_le_sub_sq`: for distinct roots `a`, `b` in `C`, `v(disc f) ≤ v(a − b)²`.
- `valuation_mapped_discr_le_sub_sq`: the same for `f` over any ring `R` mapped into the valuation ring.
- `valuation_discr_le_sub_sq_of_extension`: if `v` extends a valuation `vK` of a subfield `K` (`vK.HasExtension v`) and `f` has coefficients in the valuation ring of `vK`, then `v(disc f) ≤ v(a − b)²` for distinct roots `a`, `b` in `C`.
- Additive forms: `additiveValuation_two_nsmul_sub_le_discr`, `additiveValuation_two_nsmul_sub_le_discr_of_extension`; also `additiveValuation_discr_nonneg`, and `additiveValuation_discr_ne_top` when `f` is separable over `C`.

## Proofs

The Bezout identity comes from Mathlib's `exists_mul_add_mul_eq_C_resultant`; evaluating it at `z` gives the bound by the maximum. The divisibility by `(a − b)²` uses multiplicativity of the resultant in its first argument and the values `f′(a) = (a − b)·g(a)`, `f′(b) = (b − a)·g(b)`.

## Points to watch

- Valuations are multiplicative; the additive forms reverse the inequalities.
- The root bounds need no separability: they hold trivially when the discriminant is zero.
- `Polynomial.Monic.discr_map` and `Polynomial.sq_sub_dvd_discr` are declared in Mathlib's namespace `Polynomial`.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Mathlib/RingTheory/PolynomialDiscriminant.lean` (SHA-256 of the source file `8aaf6bb913c5becaeeffdef7c7e5af3c1abf743932845171d2a93227ccdb38b1`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).

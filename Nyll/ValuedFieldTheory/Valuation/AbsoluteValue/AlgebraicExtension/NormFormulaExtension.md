# Extensions of a henselian absolute value: integral closure and the norm formula

Module `Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormulaExtension`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `v` be a nonarchimedean absolute value on a field `K` whose valuation ring `𝒪_v` is henselian in the library's factorization sense. The file gives two statements. Over an algebraic extension, the extension of `v` is described by a valuation ring, namely the integral closure of `𝒪_v`. Over a finite extension `L`, the extension is the absolute value `x ↦ v(N(x))^(1/[L:K])`, with `N` the field norm from `L` to `K`, and it is unique among nonarchimedean extensions.

## Main results

- `henselianValuation_iff_henselFactorization`: the predicate `HenselianValuationByFactorization` for the valuation of `𝒪_v` is equivalent to `HenselFactorizationProperty` of `𝒪_v`. Both are the library's own notions.
- `normFormula_algebraic_extension`: for `L/K` algebraic, there is a unique valuation subring `W` of `L` with two properties. The valuation of `𝒪_v` extends to that of `W` (Mathlib's `Valuation.HasExtension`), and `W` equals the integral closure of `𝒪_v` in `L`.
- `absoluteValueValuation_hasExtension_of_extends`: if a nonarchimedean `w` on `L` restricts exactly to `v`, the valuation of the valuation ring of `w` extends that of `𝒪_v`.
- `normFormula_finite_normFormulaAbsoluteValue_eq_of_valuationSubring_eq_of_henselFactorization`: let `w` be a nonarchimedean extension of `v` with the same valuation ring as the norm-formula absolute value. Then `w` equals it pointwise.
- `normFormula_finite_extension_norm_formula`: for `L/K` finite, the norm-formula absolute value has four properties. It is nonarchimedean, it restricts to `v`, its value at `x` is `v(N(x))^(1/[L:K])`, and every nonarchimedean absolute value on `L` restricting to `v` equals it.

## Proofs

Uniqueness rests on an imported lemma: under the factorization hypothesis, every valuation extending that of `𝒪_v` has the integral closure as its valuation ring. To pass from equal valuation rings to equal absolute values, consider `z = xⁿ / N(x)` for `x ≠ 0`, with `n = [L:K]`. Its norm-formula value is `1`. So `z` and `z⁻¹` both lie in the common valuation ring, hence `w(z) = 1`, and therefore `w(x)ⁿ = v(N(x))`.

## Points to watch

- Henselianity is a hypothesis in the library's factorization form, standing for Hensel's lemma. Completeness is not assumed here.
- In `normFormula_algebraic_extension`, the integral-closure condition is part of the property whose uniqueness is asserted. As stated, uniqueness is therefore immediate. The stronger fact, that every extension has the integral closure as its ring, is the imported lemma used in the proof.
- In the finite theorem, uniqueness is stated only among nonarchimedean extensions of `v`.
- Extensions are exact: `w` must restrict to `v` itself, not to an equivalent absolute value.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/AbsoluteValue/AlgebraicExtension/NormFormulaExtension.lean`: the Lean file is the source byte for byte (SHA-256 `112bbd735ad69571530f27b1d7c6e2758afb61e526e51a6f3e73cb3f15658ff5`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.

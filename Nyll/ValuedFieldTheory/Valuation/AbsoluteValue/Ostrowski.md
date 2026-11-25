# Ostrowski's theorem for complete archimedean fields

Module `Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.Ostrowski`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

A field complete for an archimedean real-valued absolute value is isomorphic to `ℝ` or `ℂ`, and the absolute value is the standard one carried over by that isomorphism and raised to a fixed exponent `s` with `0 < s ≤ 1`.

## Main results

- `charZero_of_not_isNonarchimedean`: a field with an absolute value `v` that is not nonarchimedean has characteristic zero.
- `AlgEquiv.norm_symm_apply_eq_norm_rpow`: if `F` is a normed field with an `ℝ`-algebra structure whose scalars satisfy `‖r‖ = |r|^s` for some `s > 0`, then any `ℝ`-algebra isomorphism `e : F ≃ ℂ` satisfies `‖e⁻¹ z‖ = |z|^s`.
- `ostrowski_of_complete`: for `v : AbsoluteValue K ℝ` with `WithAbs v` complete and `v` not nonarchimedean, there is `s ∈ (0, 1]` and either a ring isomorphism `σ : K ≃+* ℝ` or `σ : K ≃+* ℂ` with `v a = ‖σ a‖^s` for all `a`.

Everything else in the file is private.

## Proof

In positive characteristic `v` is bounded on the integers, hence nonarchimedean. In characteristic zero the restriction of `v` to `ℚ` is archimedean, so by Mathlib's Ostrowski theorem for `ℚ` it equals `|·|^s`; the bound `v(2) ≤ 2` gives `s ≤ 1`. Completeness extends `ℚ → K` to a ring map `ℝ → K` through rational Cauchy sequences, with `‖r‖ = |r|^s`. A version of the real Gelfand–Mazur argument (minimizing the norm of `x² − a x + b`), redone for this scalar norm, shows every element is a root of a monic real quadratic, so `K` is algebraic over `ℝ` and hence `ℝ` or `ℂ` by Mathlib. In the complex case, a power-boundedness argument shows that unit complex numbers have norm 1, which yields the formula for the norm.

## Points to watch

- For `s < 1` the `ℝ`-algebra structure built on `K` is not a Mathlib `NormedAlgebra`; this is why the file redoes Gelfand–Mazur instead of using Mathlib's version.
- The isomorphisms `σ` are stated only as ring isomorphisms; continuity is not part of the conclusion.
- Completeness is the hypothesis `CompleteSpace (WithAbs v)`, and archimedean means `¬ IsNonarchimedean v` (failure of the strong triangle inequality).

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/AbsoluteValue/Ostrowski.lean`: the Lean file is the source byte for byte (SHA-256 `15de47a9ba9864cccc22ad124c255a8b3d4e4938c60eb8ebcfd3a4b73ad576d3`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.

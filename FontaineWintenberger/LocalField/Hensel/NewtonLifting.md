# Newton–Hensel lifting when the derivative is not a unit

Module `FontaineWintenberger.LocalField.Hensel.NewtonLifting`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a nontrivially normed field with ultrametric distance and `𝒪[K]` its valuation ring (the closed unit ball). The file proves Hensel's lemma in the strong form: a polynomial `F` over `𝒪[K]` and a point `a` of `𝒪[K]` with `‖F(a)‖ < ‖F′(a)‖²` give a root of `F` near `a`, when `K` is complete.

## Main results

- `unitBall_polynomial_norm_sub_le`: for `F` over `𝒪[K]` and `x, y` in `𝒪[K]`, `‖F(x) − F(y)‖ ≤ ‖x − y‖`.
- `unitBall_polynomial_norm_sub_eq_of_norm_lt_derivative`: if `‖z − a‖ < ‖F′(a)‖`, then `‖F(z) − F(a)‖ = ‖F′(a)‖ · ‖z − a‖`.
- `unitBall_hensel_nonunit`: assume `K` complete and `‖F(a)‖ < ‖F′(a)‖²`. Then there is `z` in `𝒪[K]` with
  - `F(z) = 0`;
  - `‖z − a‖ < ‖F′(a)‖`;
  - `‖F′(z)‖ = ‖F′(a)‖`;
  - `‖z − a‖ = ‖F(a)‖ / ‖F′(a)‖`;
  - every root `z′` in `𝒪[K]` with `‖z′ − a‖ < ‖F′(a)‖` equals `z`.

## Proof

The file's header says the estimates generalize the proof of Mathlib's `p`-adic Hensel lemma. With `T = ‖F(a)‖ / ‖F′(a)‖²`, a private Newton sequence `z ↦ z − F(z)/F′(z)` is built, each term carrying the invariant `‖F′(z_n)‖ = ‖F′(a)‖` and `‖F(z_n)‖ ≤ ‖F′(a)‖² · T^(2^n)`. The division is made in `K`, and the invariant shows the quotient lies in `𝒪[K]`. The ultrametric inequality makes the sequence Cauchy; its limit in the complete ring `𝒪[K]` (`unitBall_completeSpace`) is the root. The exact distance comes from the second result above, and uniqueness from the second-order Taylor expansion `Polynomial.binomExpansion`.

## Points to watch

- No discreteness of the valuation and no hypothesis on the residue field are used; completeness is needed only for the last theorem.
- The derivative at `a` need not be a unit; the hypothesis forces it to be nonzero.
- Uniqueness is among roots in `𝒪[K]` only.
- The Newton sequence and its lemmas are private.

## References

Serre, *Local Fields*, Chapters I–II.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/LocalField/Hensel/NewtonLifting.lean` (SHA-256 of the source file `0360d53d9c655832965743697a4f017f87ce654ffecb94e1727c2cf519321ac7`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).

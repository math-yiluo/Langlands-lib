# Frobenius independence modulo an absolutely irreducible plane curve

Author: Worker 78. The Lean interface was fixed by Worker 5406 for the
Stepanov norm-polynomial construction (Task 5406).

## Provenance

This module proves a form of Hilfssatz 3 of Wolfgang M. Schmidt, *Zur
Methode von Stepanov*, Acta Arithmetica 24 (1973), printed p. 350. The
registered source is `schmidt-1973-zur-methode-von-stepanov`.

Schmidt's setting is as follows. Let `f(X, Y)` be absolutely irreducible
over `F_q`, of degree `n` in `Y` and degree at most `m` in `X`. Let
`𝔜, 𝔛 = X^q, 𝔚 = 𝔜^q` be as in his (9), with `f(X, 𝔜) = 0`. Take a nonzero
polynomial

`a(X, Y, Z, W) = ∑_{i ≤ n-1} ∑_{j ≤ N} ∑_{k ≤ n-1} b_{ijk}(X) Y^i Z^j W^k`

where `deg b_{ijk} ≤ q/n - mn`. Then Hilfssatz 3 states
`a(X, 𝔜, X^q, 𝔜^q) ≠ 0` in the function field.

The Lean statement is the contrapositive, written with polynomials instead
of the function field. Write `B_{jk}(X, Y) = ∑_i b_{ijk}(X) Y^i`. Then:

> If `fh` divides `∑_{j ≤ N} ∑_{k < n} B_{jk}(X, Y) X^{qj} Y^{qk}`, then
> every `B_{jk}` is zero.

Here `fh` is the curve polynomial. Divisibility by `fh` is the same as
vanishing at the generic point `(X, 𝔜)` of the curve.

There are two differences from Schmidt's printed statement.

* **Degree hypothesis.** The Lean theorem takes a bound `d` on the
  `X`-degree of the `B_{jk}` and assumes
  `n * d + m * (n - 1)^2 < q`. This is exactly inequality (16) in
  Schmidt's proof on printed p. 351, and it is the only place his proof
  uses the bound `q/n - mn`. His hypothesis therefore implies ours.
* **Absolute irreducibility.** This is the hypothesis `hirr`: `fh` is
  irreducible after the coefficients are mapped into `AlgebraicClosure F`.

## Lean statement

`Langlands.AlgebraicGeometry.LangWeil.Stepanov.frobeniusIndependence`
takes the following data:

* a finite field `F` and `fh : Polynomial (Polynomial F)`, read as
  `F[X][Y]`: the outer variable is `Y` and the inner variable is `X`. This
  is Mathlib's `Polynomial.Bivariate` convention, so
  `fh.evalEval x y = fh(x, y)`;
* `n = fh.natDegree ≥ 1`, and every coefficient `fh.coeff i` has degree at
  most `m`;
* `hirr`: `fh` stays irreducible over `AlgebraicClosure F`;
* `hd : n * d + m * (n - 1)^2 < Nat.card F`;
* a family `B j k`, where each `B j k` has `Y`-degree `< n` and all its
  coefficients have `X`-degree `≤ d`;
* `hdvd`: `fh` divides
  `∑_{j ∈ range (N+1)} ∑_{k ∈ range n} B j k * C (X^(q*j)) * X^(q*k)`,
  where `C (X^(q j))` is `X^{qj}` and `X^(q k)` is `Y^{qk}`.

It concludes that `B j k = 0` for all `j ≤ N` and `k < n`.

## Proof as implemented

The proof follows Schmidt's strategy. In place of his symmetric functions
of the conjugates `𝔚_1, …, 𝔚_n`, it uses Mathlib's resultant
`Polynomial.resultant`. Let `q = |F|` and `g0 = fh.coeff n` (the leading
coefficient in `Y`).

1. **Resultant identity and Frobenius.** Let
   `a(Z, W) = ∑ B_{jk} Z^j W^k` over `S = F[X][Y]`, defined as `auxPoly`.
   Let `f(Z, W)` be `fh` with its coefficients viewed in `S`. Define
   `P(Z) = Res_W(f, a)` with formal sizes `(n, n - 1)`.
   `exists_mul_add_mul_eq_C_resultant` gives `u f + v a = P`. Substitute
   `Z = X^q` and `W = Y^q`. Then `f(X^q, Y^q) = fh^q`, because Frobenius
   is an `F`-algebra map (`FiniteField.frobeniusAlgHom`; lemma
   `evalEval_map_frobenius`). Also `a(X^q, Y^q)` is the sum in `hdvd`.
   Hence `fh ∣ P(X^q)`.
2. **Degree box.** The resultant is the determinant of the Sylvester
   matrix. Expanding it as a sum of products (`det_mem_boxZ`,
   `resultant_mem_boxZ`) bounds every `Z`-coefficient `P_j ∈ F[X][Y]`:
   its `Y`-degree is at most `n(n - 1)` and its `X`-degree at most `n d`.
3. **Pseudo-division and base-`q` digits.** Set `δ = (n - 1)^2`. Then
   `n(n - 1) = n - 1 + δ`. Pseudo-division by `fh` (`exists_pseudoDiv`,
   by induction on `δ`) gives `g0^δ P_j = U_j fh + R_j`. Each `R_j` has
   `Y`-degree `≤ n - 1` and `X`-degree `≤ n d + m δ < q`. This is
   Schmidt's (13)–(16). It follows that `fh` divides
   `∑_j R_j X^{qj}`, whose `Y`-degree is `< n`, so the sum is zero.
   Each `Y`-coefficient of the sum is a sum of polynomials in `X`, each of
   degree `< q`, shifted by multiples of `q`. So every `R_j` vanishes
   (`eq_zero_of_sum_mul_X_pow_eq_zero`), and `fh ∣ g0^δ P_j` for all `j`.
4. **Points over the algebraic closure.** Let `K = AlgebraicClosure F` and
   `fb = fh` over `K`. Take `(x0, y0)` in `K²` with `g0(x0) ≠ 0` and
   `fb(x0, y0) = 0`. By step 3 every `P_j(x0, y0)` vanishes. So the
   resultant of `fb(Z, W)` and `a(x0, y0; Z, W)` is zero in `K[Z]`
   (`resultant_map_map`).
   `resultant_ne_zero_of_irreducible` shows the following. If `f ∈ K[Z][W]`
   is irreducible of positive `W`-degree `n`, and `g ≠ 0` has `W`-degree
   `< n`, then `Res_W(f, g)` with sizes `(n, n - 1)` is nonzero. Its proof
   passes to the fraction field by Gauss's lemma, uses coprimality there
   and then pads the degree. Therefore `a(x0, y0; Z, W) = 0`, and every
   `B_{jk}(x0, y0) = 0`.
5. **Conclusion.** Suppose some `B_{jk} ≠ 0`. By the same lemma,
   `Res_Y(fb, B_{jk}) ∈ K[X]` is nonzero. Let `x0` satisfy
   `g0(x0) ≠ 0`. Then `fb(x0, Y)` has degree `n` and splits over `K`, so
   `resultant_eq_prod_eval` writes `Res_Y(fb, B_{jk})(x0)` as a multiple
   of a product of values `B_{jk}(x0, y0)` over roots `y0`. Step 4 makes
   one factor zero. Hence `Res_Y(fb, B_{jk}) · g0` vanishes at every point
   of the infinite field `K`, so it is zero. Since `g0 ≠ 0`, the resultant
   is zero: a contradiction.

## Helper declarations (namespace `...Stepanov.FrobIndep`)

* `boxXY`, `boxZ`: additive subgroups of degree-bounded polynomials, with
  closure under products, determinants and resultants.
* `exists_pseudoDiv`: pseudo-division with control of inner degrees.
* `eq_zero_of_sum_mul_X_pow_eq_zero`: the base-`q` digit lemma.
* `resultant_ne_zero_of_irreducible`: nonvanishing of the resultant
  against an irreducible polynomial.
* `auxPoly` and its lemmas: the auxiliary polynomial
  `∑ B_{jk} Z^j W^k`, its degree, coefficients, evaluation and maps.
* `evalEval_map_frobenius`: `fh(X^q, Y^q) = fh^q`.

The module imports only Mathlib. It uses no `sorry` and no axioms beyond
`propext`, `Classical.choice` and `Quot.sound`.

# Bounded exponential polynomials with exponents of negative real part

Module `Langlands.Analysis.BoundedExponentialPolynomial`.

This module proves the elementary fact used in the proof of the lemma of §6.4 of Bernstein–Lapid,
*On the meromorphic continuation of Eisenstein series*, J. Amer. Math. Soc. 37 (2024), p. 204, in
the form needed there: all exponents have negative real part.

## Definitions

- `expPolynomial S z p t = ∑_{i ∈ S} e^{t zᵢ} pᵢ(t)` for a finite index set `S`, complex numbers
  `zᵢ` and complex polynomials `pᵢ`, as a function of `t ∈ ℝ`.

## Results

- `expPolynomial_eq_zero_of_bounded`: if `Re zᵢ < 0` for every `i ∈ S` and `expPolynomial S z p`
  is bounded on `ℝ`, then it vanishes identically. No distinctness of the `zᵢ` is assumed.
- `exists_polynomial_eval_smul`: for a function `f` in `polynomialFunctions V n` (complex
  polynomial functions of degree at most `n` on a real vector space `V`, from
  `Langlands.Global.AdelicLeadingCuspidalComponents`) and `H ∈ V`, the function `t ↦ f(t • H)` is
  a complex polynomial in `t`.

## The proof

The proof of `expPolynomial_eq_zero_of_bounded` is the difference-operator argument of the source,
arranged as an induction. Its measure is `∑ᵢ w(pᵢ)`, where `w(0) = 0` and `w(p) = deg p + 1`
otherwise. If every `pᵢ` vanishes there is nothing to prove. Otherwise choose `j` with `pⱼ ≠ 0`
and apply `F ↦ F(· + 1) - e^{zⱼ} F`. The result is again an exponential polynomial, with
polynomials `e^{zᵢ} pᵢ(X + 1) - e^{zⱼ} pᵢ` (`Polynomial.taylor`); it is bounded, and its measure is
smaller because the degree of the `j`-th polynomial drops (`degree_sub_lt_left`). By induction it
vanishes, so `F(t + 1) = e^{zⱼ} F(t)` for every `t`. Hence `|F(t)| = e^{n Re zⱼ} |F(t - n)|` for
every `n ∈ ℕ`, which tends to `0` because `F` is bounded and `Re zⱼ < 0`. For the real-line
case, the source assumes distinct exponents and nonzero coefficient polynomials, and deduces from
boundedness that every exponent has zero real part. The theorem here proves that the sum vanishes
when every exponent has negative real part, allowing repeated exponents and zero coefficient
polynomials.

`exists_polynomial_eval_smul` is proved by induction on the span: a product of `k` linear forms
evaluated at `t • H` is `t^k` times a constant.

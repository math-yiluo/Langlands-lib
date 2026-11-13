# The discriminant good set of a plane curve

Module `Langlands.AlgebraicGeometry.LangWeil.Stepanov.GoodSet`. It imports
`Langlands.AlgebraicGeometry.LangWeil.Stepanov.ResultantDegree`, which imports only Mathlib,
together with Mathlib's Gauss lemma (`Mathlib.RingTheory.Polynomial.GaussLemma`) and
`Mathlib.FieldTheory.Separable`.

## Conventions

A plane curve is given by `fh : Polynomial (Polynomial F)` over a field `F`. The outer
variable is `Y` and the inner variable is `X`, following Mathlib's
`Polynomial.Bivariate.equivMvPolynomial` convention. So `Polynomial.derivative fh` is the
`Y`-derivative, and `fh.map (Polynomial.evalRingHom x)` is the specialisation `fh(x, Y)`.
Write `n = fh.natDegree` for the `Y`-degree.

## Statements

- `natDegree_coeff_derivative_le`: over a commutative ring `R`, if every coefficient of
  `fh : R[X][X]` has `natDegree ≤ m`, then so does every coefficient of `derivative fh`.
  This is an auxiliary lemma.
- `isCoprime_of_resultant_ne_zero`: over a field `K`, let `f g : K[X]` with
  `f.natDegree ≤ a`, `g.natDegree ≤ b`, and `a ≠ 0 ∨ b ≠ 0`. If
  `f.resultant g a b ≠ 0`, then `IsCoprime f g`. This is an auxiliary lemma.
- `exists_goodSet_discriminant` (main result): let `F` be a field and
  `fh : Polynomial (Polynomial F)` be irreducible, with `derivative fh ≠ 0` and every
  coefficient of `X`-degree at most `m`. Then there is `Δ : Polynomial F` such that:
  - `Δ ≠ 0`;
  - `Δ.natDegree ≤ (2 * n - 1) * m`;
  - for every `x : F` with `Δ.eval x ≠ 0`, the specialisation
    `fh.map (Polynomial.evalRingHom x)` has `natDegree` exactly `n` and is `Separable`.

## Provenance

The result is the standard fact that the discriminant locus of the projection `(x, y) ↦ x` is
cut out by `Res_Y(f, ∂f/∂Y)`. It supplies the "good" `x`-values in the Stepanov–Schmidt count
for plane curves (W. M. Schmidt, *Zur Methode von Stepanov*, Acta Arithmetica 24 (1973)). At
those points the fibre of the curve consists of `n` distinct geometric points. The exact
hypotheses and conclusion are the interface requested by the Task 5406 proof plan. They are
not a quotation from Schmidt.

## Proof

Take `Δ = Res(fh, derivative fh)` with Sylvester sizes `n` and `n - 1`. First, `n ≠ 0`:
otherwise `fh` is a constant `C c` and its derivative vanishes.

**`Δ ≠ 0`.**

- Let `K = FractionRing F[X]` and let `φ` be the algebra map `F[X] → K`, which is injective.
- `fh` is irreducible of positive degree, so it is primitive (`Irreducible.isPrimitive`).
  By Gauss's lemma (`IsPrimitive.irreducible_iff_irreducible_map_fraction_map`; `F[X]` is a
  GCD domain), `fh.map φ` is irreducible over `K`.
- Its derivative is `(derivative fh).map φ ≠ 0`. So `fh.map φ` is separable
  (`separable_iff_derivative_ne_zero`), that is, coprime to its derivative.
- `fh.map φ` has degree `n`, and its derivative has degree `d ≤ n - 1`; write
  `n - 1 = d + k`. Using `resultant_map_map`, `derivative_map` and
  `resultant_add_right_deg`, `φ Δ` equals `(lc fh)^k` times the resultant of `fh.map φ`
  and its derivative with default sizes.
- Neither factor is zero, the second by `resultant_ne_zero` applied to the coprime pair.
  So `φ Δ ≠ 0`, and hence `Δ ≠ 0`.

**Degree.** The coefficients of `derivative fh` are `fh.coeff (k+1) * C (k+1)`, of degree at
most `m`. `resultant_natDegree_le` with `mp = mr = m` gives the bound
`(n - 1) * m + n * m`, which equals `(2 * n - 1) * m` because `n ≥ 1`.

**Good points.** Fix `x` with `Δ(x) ≠ 0`.

- By Mathlib's `resultant_deriv`, `Δ = ± lc(fh) * discr fh`. So `lc(fh)(x) ≠ 0`, and
  `natDegree_map_of_leadingCoeff_ne_zero` shows that `fh(x, Y)` has degree `n`.
- `derivative_map` and `resultant_map_map` show that the resultant of `fh(x, Y)` and its
  derivative, with sizes `n` and `n - 1`, is `Δ(x) ≠ 0`.
- `isCoprime_of_resultant_ne_zero` then gives coprimality, which is separability
  (`separable_def`).

The auxiliary coprimality lemma takes the Bézout identity
`f * p + g * q = C (Res f g a b)` from `exists_mul_add_mul_eq_C_resultant`, and multiplies it
by `C (Res f g a b)⁻¹`.

# Additive polynomials

Helper module for the proof of `TorusVectorActionLinearizationStatement` (task 3be1ce22).
It contains no published definitions or statements; everything here is internal machinery.

- `IsAddPoly f`: a polynomial `f` in `n` variables over a commutative ring `A` is additive when
  `aeval (x + y) f = aeval x f + aeval y f` for all points `x y` with values in every
  `A`-algebra `D : Type u`. `IsAddPoly₁` is the one-variable version. Closure lemmas cover sums,
  scalar multiples, negation, composition and `p`-th powers when `(p : A) = 0`.
- `part j f`: the one-variable polynomial obtained by setting all variables except `X j` to zero.
  An additive polynomial is the sum of its parts (`IsAddPoly.eq_sum_part`), and each part is
  additive.
- One-variable classification: for an additive one-variable polynomial `φ` and `i ≥ 1`, the
  `i`-th Hasse derivative is the constant polynomial `C (φ.coeff i)` (`IsAddPoly₁.hasseDeriv_eq`).
  It need not vanish: over `𝔽₂` the polynomial `X ^ 2` is additive, and its second Hasse
  derivative is `1`. The proof compares the coefficient of `Y ^ i` in the Taylor expansion
  `φ(X + Y) = ∑ i, (D_i φ)(X) Y ^ i` with that in `φ(X) + φ(Y)`. For `1 ≤ i < d`, the
  coefficient of degree `d - i` of `D_i φ` is `(d.choose i) * φ.coeff d`, while the constant
  polynomial `C (φ.coeff i)` has zero coefficient in that positive degree. This gives the
  binomial relations `(d.choose i) * φ.coeff d = 0` (`IsAddPoly₁.choose_mul_coeff`). Also
  `φ.coeff 0 = 0` (`IsAddPoly₁.coeff_zero`). Now let `A` be an algebra over a field `k` of
  characteristic `p`, so every natural number not divisible by `p` is a unit in `A`
  (`natCast_isUnit_of_not_dvd`). If `d > 0` and `φ.coeff d ≠ 0`, the binomial relations force
  `p ∣ d.choose i` for all `1 ≤ i < d`. Lucas' theorem
  (`Choose.eq_pow_multiplicity_of_choose_modEq_zero_nat`) then makes `d` a power of `p`. Hence
  only the coefficients in degrees `p ^ r` can be nonzero (`IsAddPoly₁.coeff_eq_zero`).
- `addSpan n A p` is the `A`-span of the monomials `X j ^ (p ^ r)`, defined as
  `MvPolynomial.restrictSupport`. `IsAddPoly.mem_addSpan` shows that every additive polynomial
  lies in it, and `addSpan_le_addPolys` gives the converse when `(p : A) = 0`.

This is the classical description of additive polynomials in characteristic `p`
(the `p`-polynomials of Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, 2nd ed., Definition B.1.2
and Proposition B.1.3, printed p.562 (PDF p.588), where the proof is left to the reader). The
proof here is the standard one: binomial relations from the constant Hasse derivatives, plus
Lucas' theorem.

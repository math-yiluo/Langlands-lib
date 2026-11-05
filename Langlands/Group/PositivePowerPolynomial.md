# Polynomial vanishing along nonnegative real powers

Author: Worker 1571.

This auxiliary construction isolates the polynomial step in the polar
decomposition argument of Armand Borel, *Lie Groups and Linear Algebraic Groups,
I. Complex and Real Groups*, section 6.3, printed pages 42–43. The registered
source is `borel-lie-groups-linear-algebraic-groups-2000`, retained as
`literature/Armand Borel — Lie Groups and Linear Algebraic Groups, I. Complex and Real Groups.pdf`
(SHA256 `784f2fc696cc43c5e4375b8d1414439cce180a7273caa620aa27a9c4d8d1809c`).
The current Library contains no errata note for that source.

`powerPoint x r` is the point with coordinates the real powers `x i ^ r`,
embedded by `RCLike.ofReal` in a scalar field `𝕜 : Type u`. The coordinate type
`σ : Type v` has an independent universe and need not be finite. Each
multivariate polynomial involves only finitely many coordinates and monomials.
The main theorem `eval_powerPoint_eq_zero` assumes `0 ≤ x i` for every
coordinate and vanishing at every natural exponent, including zero, and proves
vanishing at every real exponent. It uses Mathlib's real-power convention,
including its convention at zero. In particular it applies to the strictly
positive coordinates needed for a positive definite diagonal matrix.

The implemented proof replaces Borel's asymptotic argument with finite
polynomial interpolation. The elementary helper
`sum_mul_apply_eq_zero_of_moments` concerns a finite weighted sum over a field.
If the sum of `a i * (b i)^m` is zero for every natural `m`, polynomial
induction proves that the weighted sum of any polynomial evaluated at the
`b i` is zero. Finite Lagrange interpolation supplies a polynomial agreeing
with any prescribed function of `b i` on these finitely many arguments.
Repeated arguments cause no problem because the prescribed values are already
functions of the arguments.

To apply this helper, expand the multivariate polynomial into its finitely many
monomials. Write `B d` for the nonnegative real product
`∏ i ∈ d.support, (x i)^(d i)`. Multiplicativity of real powers on nonnegative
numbers rewrites the monomial value at `powerPoint x r` as `B d ^ r`.
At natural exponents this gives exactly the moments required by the helper,
with weights the original coefficients in `𝕜` and arguments `ofReal (B d)`.
Apply the helper to the function `z ↦ ofReal ((RCLike.re z)^r)`. The identity
`re (ofReal t) = t` gives the asserted real-exponent vanishing.

The source's matrix lemma uses integer powers of the exponential of a real
diagonalizable matrix. This auxiliary theorem proves the diagonal polynomial
step, in the stronger form using only natural exponents and also allowing
nonnegative coordinates. It does not assert diagonalizability, polynomial
equations for a matrix subgroup, internal polar factors, a self-adjoint
realization of an actual reductive group, or parabolic Iwasawa coverage. Those
remain separate obligations for the enclosing Iwasawa task.

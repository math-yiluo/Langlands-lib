# Coefficient comparison from vanishing polynomial scalar differences

`RationalPolynomialDifferenceComparisonStatement` is an internal arithmetic
interface for two rational polynomials `P`, `Q`, a rational scalar `r`, and any
natural `d`. In each clause it assumes that the scalar difference sequence
`n ↦ Q(n) − r P(n)` has vanishing `d`-th forward difference as a function on
all natural numbers. It asserts the following three consequences:

- The scalar difference polynomial `Q − C(r) P` equals the published Newton
  polynomial of that sequence, truncated in degree `d`.
- The coefficients in degree `d` satisfy `Q.coeff d = r * P.coeff d`.
- If additionally `P` is nonzero of exact natural degree `d` and `r` is nonzero,
  then `Q` has natural degree `d` and leading coefficient `r * P.leadingCoeff`.

The clauses include `d = 0`; neither polynomial has a degree hypothesis in the
first two clauses. The third clause explicitly includes `P ≠ 0` because the
zero polynomial also has natural degree zero.

This statement is derived from the published Newton reconstruction and its
top-coefficient formula. The next difference also vanishes, so the Newton
polynomial has the same natural evaluations as `Q − C(r) P`; polynomial
uniqueness gives equality. Its coefficient in degree `d` is zero. Its natural
degree is at most `d`, which bounds the degree of `Q` once `P` has degree `d`.
The coefficient in degree `d` is then nonzero under the third clause's
hypotheses, giving exact degree and the leading-coefficient identity. This is
pure polynomial arithmetic and supplies no geometric vanishing, exact-degree,
or native-rank premise by itself.

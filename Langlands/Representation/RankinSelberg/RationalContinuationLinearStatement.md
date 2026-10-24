# Linear combinations of rational continuations

`Langlands.RankinSelberg.RationalContinuationLinearStatement` is an internal
Prop-valued target with two algebraic closure assertions. This file supplies
the statement, not a proof.

First, for any natural number `q`, any finite family of complex functions
`f_i(s)`, rational functions `R_i`, and complex constants `c_i`, if each `R_i`
is a `HasRationalContinuation q` of `f_i`, then

```text
sum_i c_i f_i(s)
```

has continuation `sum_i RatFunc.C(c_i) * R_i`. The coefficients are independent
of `s`. The number of terms can be zero, and zero coefficients and zero
functions are allowed. The continuation uses the existing spectral point
`q^(-s)` and includes nonvanishing of the reduced denominator throughout
some right half-plane. The finitely many input half-planes may differ.
No condition `q > 1` is needed for closure; uniqueness of continuations is a
separate result that requires that condition.

Second, let `values` be any set of rational functions and let `d` be any
Laurent polynomial. If multiplication by the actual embedding
`laurentToRatFunc d` takes every element of `values` into the image of the
Laurent polynomial ring, it does the same for every element of
`zetaSpan values`. The conclusion retains exactly the same `d`. It quantifies
over the full Laurent module span, not just complex linear combinations.
The assertion does not require `d ≠ 0`; when an application supplies that
condition, the conclusion preserves the same nonzero common denominator.
It neither constructs a nonzero denominator without an input one nor
claims that pointwise rationality supplies a common denominator.

These are internal consequences of the published definitions in
`RationalContinuation` and `RationalZeta`. For the first assertion, take
finite intersections of right half-planes, use divisibility of reduced
denominators under addition and multiplication, and evaluate rational sums
and products away from their denominator zeros. Constant rational functions
have denominator one. For the second assertion, the property of having
`d * R` in the Laurent image is closed under zero, addition, and Laurent
scalar multiplication, so it contains the span of the original set.

The intended use is to combine already established Mellin continuations
and their uniform denominator bounds. No integral is replaced by an
abstract value in this statement: establishing the actual integral formula,
convergence, and each input continuation remains separate work. No
representation-theoretic hypothesis or normalized-generator assertion is
included, and no independent literature theorem is claimed.

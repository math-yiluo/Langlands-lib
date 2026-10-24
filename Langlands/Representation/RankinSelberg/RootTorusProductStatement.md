# Uniform products of torus expansions in root coordinates

`Langlands.RankinSelberg.RootTorusProductStatement F T n` is an internal
pointwise reduction for a p-adic field `F`, its supplied topological data `T`,
and every natural number `n`. It retains the universe of `F` and includes
rank one (`n = 0`).

Write `A = Fin (n + 1) → Fˣ`. For `a ∈ A`, let `d(a)` have coordinate
`d(a)_i = ∏_{j ≥ i} a_j`, and put

\[
w(a)=\left(\prod_{i=0}^{n}|a_i|_F^{(i+1)(n-i)}\right)^{-1},
\]

viewed in the complex numbers using the actual `T.normalizedAbs`. A finite
function means a continuous complex-valued function on `A` whose left
translates span a finite-dimensional complex vector space. The statement
uses exactly the translation convention `a ↦ f(b*a)`.

Given two finite sets `X` and `Y` of finite functions, the resulting family
is indexed by the finite product of their membership subtypes:

\[
\eta_{\chi,\chi'}(a)=\chi(d(a))\chi'(d(a))w(a).
\]

The statement first asserts that every member of this explicit family is
a finite function. This family depends only on `X`, `Y`, `F`, `T` and `n`;
it is fixed before all Schwartz tests and the invertible matrix `k`.
Repeated function values at different indices are permitted.

For arbitrary families of Schwartz–Bruhat functions `φ_χ, φ'_{χ'}` on
`F^n`, a Schwartz–Bruhat row test `Φ` on `F^(n+1)`, and any invertible
matrix `k`, there are Schwartz–Bruhat functions `Ψ_{χ,χ'}` on `F^(n+1)`
such that the following identity holds at every unit vector `a`:

\[
\begin{aligned}
&\left(\sum_{\chi\in X}
 \phi_\chi\bigl((d(a)_i/d(a)_{i+1})_{i<n}\bigr)\chi(d(a))\right)
 \left(\sum_{\chi'\in Y}
 \phi'_{\chi'}\bigl((d(a)_i/d(a)_{i+1})_{i<n}\bigr)\chi'(d(a))\right)\\
&\qquad\cdot\Phi\bigl(\operatorname{lastRow}
       (\operatorname{diag}(d(a))k)\bigr)w(a)
 =\sum_{(\chi,\chi')\in X\times Y}
       \Psi_{\chi,\chi'}\bigl((a_i)_{i\le n}\bigr)
       \eta_{\chi,\chi'}(a).
\end{aligned}
\]

Unit coordinates inside a test function are coerced to field elements.
In Lean the sums over `X` and `Y` are sums over their membership subtypes.
This is equivalent to the finite-set sums in `CoefficientTorusExpansion`
and avoids any choices of enumerations or distinctness assumptions.
Empty input families and zero tests are allowed.

The provenance is an internal combination of the root-coordinate identities,
finite-function product and pullback closure, and Schwartz assembly. The
adjacent ratios of `d(a)` are the first `n` coordinates of `a`, and the
displayed last row is `a_n • lastRow k`. Thus each product of three tests
can be assembled into a Schwartz function on the full field vector space.
Multiplying the two finite sums gives the displayed identity. The function
family is finite because its index set is finite; taking its image as a
finite set gives a test-independent input family for the Mellin step.

This statement supplies neither a Whittaker expansion nor an integration
formula. It assumes the two finite families and describes their product.
There is no spectral parameter, convergence, rational continuation or
denominator conclusion here. Uniform denominator control still requires
the separate Mellin result, as well as the analytic prerequisites for the
actual equal-rank integral. No separate literature theorem is attributed
to this elementary adapter. The Lean file defines its proposition target.

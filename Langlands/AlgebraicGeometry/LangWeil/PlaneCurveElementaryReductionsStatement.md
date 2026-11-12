# Elementary coordinate reductions for plane curves

Author: Worker 96.

`PlaneCurveElementaryReductionsStatement` is a proposition with two
elementary conclusions needed before the Stepanov norm construction.
Neither conclusion is proved in this module.

For an absolutely irreducible `f ∈ F[X,Y]` over any finite field, with both
partial degrees positive, its first clause produces an absolutely
irreducible polynomial `g` with the same number of rational zeros. Both
partial derivatives of `g` are nonzero, and its partial degrees are ordered:
`0 < deg_Y g ≤ deg_X g`. It retains quantitative degree control:

`deg_X g ≤ max(deg_X f,deg_Y f)` and
`deg_Y g ≤ min(deg_X f,deg_Y f)`.

Thus the numerical threshold and error coefficient for `g` can be bounded
by those for `f`. This conclusion asserts no point-count estimate.

The second clause treats `deg_Y f = 1`: the difference between its
rational zero count and `#F` has absolute value at most `deg_X f`.
No nonzero partial derivative or positive `X`-degree hypothesis is needed
for this clause.

Provenance: derived elementary reduction, motivated by Section 2, printed
p.349 (PDF page 2, right half), of Wolfgang M. Schmidt,
*Zur Methode von Stepanov*, Acta Arithmetica 24 (1973),
registered source `schmidt-1973-zur-methode-von-stepanov`, SHA256
`a46364b77f152a1656fa6d60181492cfb868803eae767a2145be38fd20bbdd4d`.
That passage removes polynomials in `X^p` and then in `Y^p`, using the
Frobenius automorphism of the finite field, and orders the degrees as
`2 ≤ n ≤ m` after treating the linear cases.

The first clause packages that reduction with explicit degree inequalities
and zero-count equality. In characteristic `p`, zero partial derivative in
`X` means that every `X` exponent is divisible by `p`. Writing
`f(X,Y)=h(X^p,Y)` preserves the number of rational zeros, since
`x ↦ x^p` permutes `F`. It preserves absolute irreducibility: a
factorization of `h` over the algebraic closure would give one of `f`
after substitution, and substitution preserves nonconstant factors.
Repeating in either coordinate terminates because the positive partial
degree strictly decreases. Exchanging the two coordinates then orders the
degrees; sorting two individually decreased degrees yields the displayed
maximum and minimum bounds.

The second clause follows by writing `f=a(X)Y+b(X)`. Irreducibility and
positive `Y`-degree imply that `a` and `b` have no common root in `F`.
Every `x` with `a(x) ≠ 0` gives exactly one zero of `f(x,Y)`, while an
`x` with `a(x)=0` gives none. There are at most
`deg a ≤ deg_X f` such exceptional `x`. In particular, the clause is an
inequality and does not assert that the rational zero count is always `q`.

These are algebraic and finite-counting prerequisites. They assume no
Lang–Weil or Hasse–Weil theorem, no Riemann–Roch theorem, and no
unconstructed geometric model.

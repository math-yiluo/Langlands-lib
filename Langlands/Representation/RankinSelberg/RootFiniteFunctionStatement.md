# Finite functions with the inverse root-coordinate modulus

`Langlands.RankinSelberg.RootCoordinateFiniteFunctionStatement F T n`
is a supporting proposition for every prime, p-adic field `F`, supplied
`F.TopologicalData T`, and positive rank `n + 1`, including rank one. It uses
the supplied topology, the torus `A = Fin (n + 1) → F.Carrierˣ`, and the
explicit suffix-product map

\[
d(a)_i=\prod_{j\ge i}a_j.
\]

It defines locally the complex weight

\[
w(a)=\left(\prod_{i=0}^{n}
 |a_i|_T^{(i+1)(n-i)}\right)^{-1},
\]

where the real normalized absolute values are cast into `ℂ` before taking
natural powers and the reciprocal. The proposition asserts continuity of
`w`, `w(1) = 1`, and `w(ab) = w(a)w(b)`.

It then states that for every two continuous complex functions `f,g` on `A`
whose left translates span finite-dimensional complex spaces, the function

\[
a\longmapsto f(d(a))g(d(a))w(a)
\]

has those same two properties. As in `CoefficientTorusExpansion`, left
translation means the function `a ↦ f(b * a)`, with all `b : A` included in
the span. The assertions impose no smoothness, nonvanishing, irreducibility,
or character-decomposition hypothesis on `f` or `g`. The functions are
arbitrary, so the closure assertion can be applied to every pair in two
fixed finite families. It does not itself assert a denominator bound.

This is an internal adapter derived from published interfaces rather than a
separate theorem attributed to an original source. The precise suffix-product
map and exponent formula come from `RootCoordinateChangeStatement`; its final
clause identifies the positive Borel modulus in these coordinates with the
product appearing above. Thus `w` is its reciprocal. The arbitrary-function
closure assertion specializes `FiniteFunctionClosureStatement` to that
coordinate map and multiplicative weight. Continuity of the normalized
absolute value is supported by the published topology identification and
`normalizedAbs_eq_canonicalNorm_pow_degree` in the normalization theory.
The statement module asserts these properties as a proposition target and
does not supply proofs.

No quotient integration, Whittaker expansion, Schwartz coefficient assembly,
Mellin convergence, rational continuation, common denominator, or normalized
generator is asserted. Those are separate steps in the equal-rank analytic
argument. In rank one the weight is identically one because every displayed
exponent is zero.

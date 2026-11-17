# Commutator transport with separate powers on the root terms

This internal derived module transports a literal actual commutator
formula through separately supplied power maps on its two inputs and
its individual terms. It records the scalar equations that must be
checked for varying root factors.

`CommTermPowerData` specifies an actual additive-line endomorphism,
its exponent, and a new coefficient and two new degrees.
`CommTermPowerData.applyTo` precomposes the map in the original term
by that endomorphism and inserts the new coefficient and degrees.

For input powers `a` and `b`, the predicate `IsBalanced` requires the
actual all-test power formula for the specified term endomorphism and
three equations. If the original term is `w(c x^i y^j)` and the new
data have exponent `d`, coefficient `c₀` and degrees `i₀`, `j₀`, these
equations are

`c₀^d = c`, `i₀*d = a*i`, and `j₀*d = b*j`.

They imply that the transformed term at `(x,y)` is exactly the
original term at `(x^a,y^b)` on every scheme test.
`powerCommTermsWith` performs these transformations in the supplied
list order. `CommRel.precompose_balanced_powers` evaluates the original
commutator formula at the two powered arguments and applies the
termwise equalities to obtain the new formula.

All maps and their point formulas are supplied explicitly; the result
does not infer the existence of a power homomorphism from an unstated
characteristic condition. No positivity, field, localness, reducedness
or nontriviality hypothesis is imposed on the base ring. The coefficient
and degree equations remain obligations, and the module neither
permutes terms nor deletes vanishing ones. Thus it is a transport
interface for the exceptional rank-two checks, rather than a proof of
those checks.

The provenance is the imported actual-point transport result and
commutative-ring power arithmetic, followed by equality of the ordered
lists of actual terms.

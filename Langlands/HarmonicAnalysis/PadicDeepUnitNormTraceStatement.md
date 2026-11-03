# First-order character compatibility with actual norms

Worker 84 specifies the internal target
`Langlands.HarmonicAnalysis.PadicDeepUnitNormTraceStatement.{u,v}`.
This module defines a target and contains no proof. Workers 84 and 27 are
coauthors for the supplied-integer determinant/localization derivation.

For all finite compatible p-adic field extensions E/F in independent universes,
all supplied topological data T and S, a continuous nontrivial additive unitary
character psi of F, scalar c, natural level n and continuous complex character
chi of F units, suppose chi agrees with Circle.toUnits(psi(c*(u-1))) on every
actual T.principalUnits n. For an actual integer a of F assume v(a)<1,
v(a)<=exp(-n) and v(c)*v(a)^2<=exp(conductor psi). For every actual integer y
of E, the target constructs an actual field unit z=1+i(a)y. Its actual determinant
norm belongs to T.principalUnits n and chi(N(z)) equals
Circle.toUnits(psi(c*a*Tr(y))). No finite-order premise on chi is needed for this
comparison. All primes, including two, level zero and a=0 are included.

This is an internal consequence of integral trace transport, the integral
quadratic norm-trace identity, valuation bounds and the actual additive conductor.
It is not attributed to an original-source theorem. Integrality of Tr(y) and the
quadratic error bound show v(N(z)-1)<=v(a)<1, hence N(z) is a nonzero valuation
unit at the required depth. Nonzero norm makes z nonzero. The quadratic error
in the character argument is killed by the conductor, giving the displayed exact
identity. The complete private proof is separate from this statement candidate;
no independent mathematical acceptance is asserted here.

This supplies the finite-extension norm-coordinate comparison needed in the
first-order H2 route. Additive trace transitivity through an intermediate field,
a primitive coefficient, simultaneous detection under automorphisms, arbitrary
depth and the exact stabilizer remain additional obligations.

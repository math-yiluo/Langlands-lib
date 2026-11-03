# Coefficient change for actual scheme points

Author: Worker 105.

These targets use the actual relative point sets `RingPoint R X S` and
`RingPoint R X T` of every scheme X over Spec R. The coefficient map is the
existing `RingPoint.changeRing f`, namely precomposition with Spec(f) over
Spec R. Both point topologies are explicitly `schemePointTopology`, the final
topologies from all actual affine open charts. R has no topology. The base
and both value rings lie in an arbitrary common universe.

`SchemeCoefficientContinuityProperty` says that a continuous R-algebra map
f : S → T gives a continuous map on these point spaces. It requires only
commutative rings, their specified R-algebra structures and topologies on
S and T. It needs no local-ring, topological-ring, unit, finiteness or
separatedness assumptions. This is a formal property of the specified final
topologies, including when the value rings are not local.

`SchemeCoefficientOpenProperty` separately assumes that S and T are local
topological rings, T satisfies `IsOpenUnits`, f is an open embedding, and X is
locally of finite type over Spec R. It says that the actual coefficient map
on X-points is open. No unit condition on S, quasi-compactness of X or
separatedness of X is assumed. No injectivity conclusion is included.
`SchemeCoefficientProperties` combines these statements with their separate
hypotheses.

This is a derived general form of the affine-local argument in Brian Conrad,
*Weil and Grothendieck approaches to adelic points* (December 31, 2011),
Theorem 3.6 proof, printed page 8, last two paragraphs before the square.
There Conrad treats finite-type schemes over a complete discrete valuation
ring O and the map X(O) → X_K(K): the affine case uses that O^n is open in K^n,
and open-subscheme point sets cover X(O), reducing continuity and openness to
the affine case. The present targets isolate the coefficient-map argument
for the already constructed chart-final topology. Continuity uses its final
property. Openness uses local S for affine-chart coverage, the finite-type
affine coefficient embedding, and local T with open units for open target
chart maps. Thus neither completeness nor global finite type is needed for
this generalization.

The original proof invokes separatedness separately for injectivity.
These targets do not assert that conclusion, a base-change comparison with
X_T(T), DVR specialization, adelic transition properties or whole-paper
completion; those are separate obligations.

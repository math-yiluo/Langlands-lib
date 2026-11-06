# Quadratic SU3 coordinates over henselian integer-valued fields

Worker 1620 specializes `FieldTheory.henselianIntegerAddValuation` to an
actual separable quadratic extension. The trace inequality, scalar translation
and cofinal central-coordinate arguments adapt Worker 1676's published
`SU3RootParametersLocalValuation` proofs. Both workers are coauthors of this
internal derived construction.

The base and extension fields have independent universes. The valuation is any
integer-valued valuation with a Henselian valuation subring; the extension is any
actual separable quadratic field extension. No topological, completeness,
residue-field or characteristic restriction is imposed. Surjectivity of the
base valuation is needed only for integer translates and cofinal coordinates.
The imported local-valuation module supplies the purely algebraic theorem
`exists_ne_zero_traceZero`; no local-field instance is used here.

`henselianQuadraticValuation` is the invariant additive prolongation normalized
to the negative integer logarithm of the base valuation. Conjugation and the
associated ring involution preserve it. On embedded base units the value is
exactly `Geometry.Building.IntegerValuation.order`, the real order in the
apartment target. Finite Galois norm calibration specializes to degree two,
and every nonzero extension element has value `n / 2` for an integer `n`.
Containment in the half-integers is asserted, without surjectivity onto them.

The actual embedded field trace is `x + conjugation x`. The additive valuation
inequality and invariance therefore give `value(x) ≤ value(trace(x))`,
including when either element is zero.

Surjectivity of the base valuation supplies a scalar with value
`WithZero.exp (-n)`, whose additive order is the prescribed integer `n`.
It is nonzero, and its embedded additive value is exactly `n`.
Multiplication by this scalar preserves the actual trace-zero subgroup because
conjugation fixes it, and translates the value by `n`. Given a real bound,
start with the nonzero trace-zero element and choose an integer translate
above the difference between the bound and its finite value. The parameter
`(0,w)` satisfies the coordinate equation, lies in the central subgroup, and
has nonzero second coordinate of value at least the bound.

These are intrinsic field and coordinate results derived from the imported
Library modules. They do not identify the coordinates with arbitrary relative
root groups or prove apartment existence, normalizer stability or full
centralizer compatibility.

# Noetherianity of the actual arithmetic S-integer rings

Author: Worker 208.

`AdelicSIntegersNoetherianStatement` combines two arithmetic targets,
each asserting that the actual S-integer ring is Noetherian and has
Krull dimension at most one. `Ring.DimensionLEOne` expresses the latter
for these commutative domains. The fields occupy one arbitrary common
universe.

The function-field clause quantifies fields `k` and `F`, their compatible
`k`- and `RatFunc k`-algebra structures, `FunctionField k F`, and every
finite set `S` of the actual `AlgebraicCurve.Place k F`. Its ring is the
published subring `curvePlaceSIntegers k F S` of `F`: an element belongs
exactly when it lies in the original valuation ring at every place
outside `S`. It uses the existing constant action, given by restricting
the original inclusion of `k` into `F`. There is no finite-constant,
perfectness, separability, nonempty-`S` or affine-model hypothesis.

The number-field clause quantifies a number field `K` and every finite
set `S` of its actual finite places. Its ring is Mathlib's
`(S : Set (FinitePlace K)).integer K`, the actual subalgebra of `K`
consisting of elements integral outside `S`. The number-field level
convention includes all infinite places separately; they impose no
integrality condition on this ring.

This is a derived arithmetic prerequisite for Brian Conrad, *Weil and
Grothendieck approaches to adelic points* (December 31, 2011), printed
pp.1 and 6–8, especially the S-integer bases and finite-type models in
Theorem 3.6. Registered source:
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The statement is not a quotation or a numbered result of that paper.
It is obtained from one-dimensional overring arithmetic: the published
`Subalgebra.isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite`
applies to the number-field ring over its ring of integers. For a
function-field subalgebra, a transcendental element gives a polynomial
parameter over which the ambient field is finite; if every element is
algebraic over the constants, the subalgebra is a field. This also
explains why empty `S` causes no exception to this target.

Proof publication is separate. This statement alone does not identify
the function-field ring with an affine curve model, prove finite type
over the constants, identify its spectrum or fraction field, or prove
any finite-type geometric or topological comparison. Conrad's
nonempty-`S` convention in positive characteristic still applies to
those later model applications. Model descent, nonaffine point
topologies, the adelic colimit, algebraic spaces and the remaining
whole-paper assertions remain separate obligations.

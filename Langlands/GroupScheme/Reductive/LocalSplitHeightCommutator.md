# Positive weight bounds for commutators on every scheme test

This internal supporting result uses the universal commutator polynomials
already proved in `Reductive.LocalSplitCommutatorPolynomials`. It is valid
over any commutative ring, in universe `u`, including rings with nilpotents
and the zero ring.

`lineEvalSections` evaluates `R[S][T]` in the global sections of an arbitrary
scheme `Z` over `Spec R`. The morphism `commutatorLinePoint` classifies those two
sections, using the usual adjunction between global sections and Spec.
Pulling the defining universal commutator identity back along this map proves
`IsUnivComm.posComm_eq_sections`. Thus specialization works on all scheme
tests without an affineness hypothesis.

For a split torus acting equivariantly on the supplied additive factor maps,
and an open big-cell map, `IsUnivComm.coPairing_eq` pairs each nonzero
bihomogeneous commutator monomial with any cocharacter. The two exponents
are at least one by the published universal-polynomial theorem. Consequently,
if the input weights are nonnegative, the coordinate polynomial at any
weight strictly below their sum is zero.

`exists_posComm_eq_weight_ge` applies this vanishing to the universal
coordinates and specializes them on any scheme test. It yields an ordered
factorization of the commutator with every coordinate below the sum of the
two positive input weights equal to zero. The negative and positive
cocharacter hypotheses are exactly those needed by the published existence
theorem for universal coordinates.

The proof uses the published polynomial scaling identity and elementary
integer inequalities. It is a derived algebraic part of the weighted-root
construction used in Conrad, *Reductive group schemes* (2014),
Theorem 5.4.3, pp.174–177. It does not construct filtration group schemes,
represented quotients, vector-bundle descent, or a finite series. Those
belong to the finite vector-bundle filtrations of supplied relative radicals,
outside this module.

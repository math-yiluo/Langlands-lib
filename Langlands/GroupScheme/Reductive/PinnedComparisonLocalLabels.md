# Local completeness of full weight labels for pinned comparisons

This internal development supports the pair classification motivated by Conrad,
*Reductive group schemes* (2014), Theorem 6.1.17, p. 197, and the all-test
argument for Theorem 7.1.9(3), pp. 245–246, source
`conrad-2014-reductive-group-schemes`.

The implemented coefficient argument uses the universal adjoint coefficients
to show that a chosen nonzero simple pinning vector determines its integral
weight over any nonzero ring. On a local coefficient ring, the concrete
local-pinning predicate identifies each source chosen vector with a target
chosen vector. An exact full torus square puts its image in the weight space
specified by the based root equivalence. Uniqueness of the vector's weight and
injectivity of the root indexing force the pinning correspondence to be the
specified one. Thus the comparison satisfies the exact affine pinned
isomorphism theorem's predicate.

Actual comparisons on an arbitrary common scheme are equal if their pullbacks
along every local-ring spectrum are equal. The proof projects to the original
affine target group and uses detection by local-ring points, retaining
nilpotent structure.

With the affine pinned isomorphism theorem as an explicit premise,
`eq_fixedComparison_of_locallyPinned` therefore identifies a concretely
locally pinned comparison with the canonical fixed comparison whenever its
full torus action is fixed. On each local coefficient test both comparisons
satisfy the exact affine theorem's predicate, so its uniqueness applies.
Detection by local-ring points then gives equality on the original common
scheme.

Finally, `exists_open_comparisonLabel` uses the Library's open based-coordinate
alignment near each point. Its full weight map supplies a `ComparisonLabel`.
The chosen root-datum witness for this label may differ from the one supplied
by the alignment, but their weight maps agree. The all-test monomial formula
therefore identifies the actual torus map with the label's fixed torus map.
The preceding rigidity theorem proves equality of the pulled-back comparison
with the label's canonical representative on that open neighbourhood.
The common scheme is arbitrary, and the pointwise conclusion is vacuous for
the empty scheme. No global constancy on disconnected schemes is asserted.

`LabeledComparisonNeighbourhood` packages the open, its point membership,
the full lattice label, and the exact comparison equation.
`labeledComparisonNeighbourhood` chooses this data for each concretely locally
pinned comparison and point using the proved local completeness theorem.

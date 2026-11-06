# Degree zero of actual automorphic horizontal cohomology

This internal construction computes degree zero of the existing horizontal
cohomology of an `OperatorRealization F n`. Here `F : Type u` is any number
field, `n` is a positive natural rank, and coefficients are the actual complex
module `S.Space` of stable automorphic functions in the supplied realization.

`S.horizontalJointInvariants` is the submodule of vectors fixed by every
element of the full standard infinite compact group and killed by every
element of `ReducedComplexLieAlgebra F n` under `S.reducedLieAction`.
`mem_horizontalJointInvariants` states precisely these two universal
conditions. The full compact group, including all its components, is used.

`horizontalCyclesDegreeZeroEquiv` identifies the original closed horizontal
zero cochains with this submodule. Evaluation at the unique empty tuple gives
the forward map; the inverse is the constant zero cochain with the supplied
coefficient value. The two evaluation lemmas state these formulas on the
original alternating-map carrier.

`horizontalBoundariesInCycles_zero` proves that the existing boundary
inclusion range inside the cycle module is bottom in degree zero.
`horizontalDegreeZeroEquiv` consequently has the exact domain
`S.HorizontalCohomology 0`, the original quotient of these cycles by these
boundaries. It identifies that quotient with `S.horizontalJointInvariants`.
The class formula sends the original quotient projection of a zero cycle to
its coefficient value. The inverse formula uses the original projection of
the constant zero cycle; a nonzero invariant has a nonzero inverse class.

The implementation specializes
`Langlands.Cohomology.Lie.Horizontal.degreeZeroEquiv` and its cycle and
boundary constructions. The horizontal subspace is
`compactInReducedSubmodule F n`, the Lie-algebra group action is
`reducedCompactRepresentation F n`, and the coefficient group action is
`S.compactRepresentation`. Bracket covariance comes from the actual reduced
conjugation Lie equivalence, coefficient covariance from
`S.compactRepresentation_reducedLieAction`, and the all-degree insertion
identity from `S.horizontalCochain_infinitesimal`. All compatibility premises
of the generic construction are thus discharged by existing actual-action
theorems. No cochain carrier, differential or compatibility witness is supplied
as a new input.

Provenance is internal: this is a specialization of the existing generic
degree-zero computation to the actual automorphic quotient. No new external
source identification, geometric comparison, automorphic occurrence or
unconditional nonvanishing is claimed. The nonvanishing lemma requires an
actual nonzero simultaneous invariant.

Authorship: Worker 2.

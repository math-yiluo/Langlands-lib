# Actual relative cohomology of automorphic analytic coefficient tensors

This internal construction uses the original actual automorphic space
`S.Space`, the full genuine analytic coefficient module `AnalyticSpace e ρ`,
their original diagonal compact representation, and their constructed diagonal
complex Lie action. `analyticTensorReducedLieRingModule` and
`analyticTensorReducedLieModule` restrict the latter through
`reducedComplexInclusion`. The resulting bracket is exactly the existing
`tensorReducedLieAction`. The already proved full compact covariance, evaluated
on that inclusion, gives `tensorAnalyticCompactRepresentation_reduced_lie`.
No coefficient covariance premise is supplied.

For the differential and cohomology, assume `NeZero n`, as required by the
actual split-center retraction used in the existing reduced cochain extension.
`tensorAnalyticReducedCochain_compact` extends an actual reduced alternating
cochain to the full complex Lie algebra using `reducedComplexProjection`.
The public extension theorem preserves full compact equivariance.
Apply the derived tensor compact insertion theorem to that extension, then
restrict the tuple through `reducedComplexInclusion`. The retraction and
bracket identities give the reduced insertion law. Thus this law is proved
from original full compact equivariance, with no infinitesimal compatibility
certificate.

`tensorAnalyticHorizontal_infinitesimal` applies this reduced insertion law to
the actual image `compactInReducedSubmodule`. These are precisely the
infinitesimal identities required by the published
`horizontalEquivariantDifferential`. Together with actual adjoint bracket
preservation and the proved tensor coefficient covariance, they construct
`tensorAnalyticHorizontalDifferential` on the original full-compact-equivariant
horizontal tensor cochains. Its underlying alternating map is the genuine
Chevalley–Eilenberg coefficient differential. Its square is zero by the
published square-zero theorem for that differential.

The remaining definitions specialize the published actual horizontal
cohomology construction with all its premises discharged:

- `tensorAnalyticHorizontalCycles` is the kernel of this actual differential.
- `tensorAnalyticHorizontalBoundaries` is zero in degree zero and the actual
  preceding differential's range in successor degrees.
- `tensorAnalyticHorizontalBoundariesInCycles` is the range of the genuine
  boundary inclusion inside cycles. Square zero proves that inclusion.
- `TensorAnalyticHorizontalCohomology` is the quotient of that actual cycle
  module by that actual boundary submodule.
- `tensorAnalyticHorizontalClass` is the actual linear quotient projection.

The specialized class laws prove surjectivity, characterize zero classes by
actual boundary membership, and characterize equality of classes by boundary
membership of their difference. The actual differential with codomain
restricted to cycles has zero cohomology class. These are applications of the
published horizontal cohomology laws to the constructed objects, rather than
new assumptions about a cohomology type.

The number-field universe remains independent of the small finite
selected-embedding and coefficient indices. Both selected complex-place
orientations, the entire coefficient carrier, empty finite indices and every
cochain degree are retained. The reduced action and covariance precede the
positive-rank hypothesis; reduced insertion, differential and cohomology use
that explicit hypothesis. No topology on the automorphic or tensor spaces is
introduced. Finite adelic action on this cohomology and analytic-algebraic
cohomology transport are subsequent constructions.

The provenance is internal restriction and composition of the actual tensor
compact differentiation, reduced cochain extension, coefficient differential
and quotient cohomology constructions. No new original-source correspondence
is claimed.

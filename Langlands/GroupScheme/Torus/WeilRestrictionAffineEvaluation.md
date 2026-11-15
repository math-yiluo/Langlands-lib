# Affine pullback evaluation of Weil-restriction points

Let \(A\) and \(B\) be commutative rings with an \(A\)-algebra structure on
\(B\). For a test \(U\) over \(\operatorname{Spec} A\), `coefficientTest`
is \(U_B\), its pullback to \(\operatorname{Spec} B\).
`coefficientProjection` is the projection to \(U\), regarded over
\(\operatorname{Spec} A\); its naturality is proved on every test.

For affine \(U\), `affinePullbackSectionsIso` identifies
\(\Gamma(U,\mathcal O_U)\otimes_A B\) with the actual global sections of
\(U_B\). The test algebra structure comes from the relative global-sections
functor. The isomorphism is the composite of the inverse
global-sections/spectrum isomorphism with pullback by the published affine
scalar-extension spectrum comparison. Taking global sections of its two
projection identities proves compatibility with each tensor factor.
`coefficientSectionsEquiv` puts the \(B\) factor first. On \(b\otimes r\)
it multiplies the pullbacks of \(b\) and \(r\).

Assume in addition that \(B\) is finite and projective as an \(A\)-module,
so that the published `WeilGm.groupScheme A B` is available.
`coefficientEvaluation` sends a Weil-restriction point on an arbitrary
test \(U\) to a unit on \(U_B\): first pull the point back by the
coefficient projection, then apply `WeilGm.evaluationUnits`. Its naturality
follows from projection naturality and the published naturality of scalar
evaluation.

For affine \(U\), `affineEvaluationEquiv` is the multiplicative equivalence
from Weil-restriction points on \(U\) to \(\Gamma(U_B,\mathcal O_{U_B})^\times\).
It composes `WeilGm.pointsEquiv` with the unit map of
`coefficientSectionsEquiv`. Tensor induction identifies this equivalence
with `coefficientEvaluation`; hence it is natural between affine tests.

These are internal constructions derived from the published point and affine
scalar-extension comparisons. No flatness or faithful flatness of \(B/A\)
is assumed. This module supplies an evaluation equivalence, without a
cocycle-vanishing or quasi-split-inner-form assertion.

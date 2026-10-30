# A rational positive skew-twist existence target

`PositiveRationalSkewTwistExists D C` is a proposition, not a proof. The
published theorem
`Langlands.Shimura.CentralSimpleUnitaryData.positiveRationalSkewTwistExists`,
in `Langlands.Shimura.Unitary.PositiveRationalTwistProof`, proves it for every
such `D` and `C`. Worker 1060 updated the proof-status paragraphs after the
2026-10-29 documentation audit (finding P3-041).
Its inputs are the actual central simple CM algebra D and a
`HarrisSignatureCharts` object C for its given involution sigma and degree n.
The charts are genuine center-compatible real matrix equivalences with
the Harris signatures.

The proposition asks for an actual rational unit beta of A and a proof
sigma(beta) = -beta such that the involution

    tau(x) = beta sigma(x) beta inverse

is positive after real scalar extension. Positivity is the existing
`AlgebraInvolution.IsPositive`: for every nonzero x in R tensor_Q A,
the real regular trace of tau(x)x is strictly positive. The tensor
extension, involution and trace in this condition are the previously
constructed ones. No desired unit or positive involution is supplied
as an input. The statement imposes no additional finite-place condition.

## Source and proof route

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), Section I.7, printed p.52 (PDF p.60), uses rational
approximation in the symmetric subspace to replace a second-kind
involution by a positive inner twist. The argument uses the nonempty
open cone of positive symmetric elements. Kottwitz, *Points on some
Shimura varieties over finite fields* (1992), Lemma 2.8, printed p.381
(PDF p.9), proves that cone is nonempty and open for a positive
involution.

The target here is a derived skew-unit version adapted to the already
constructed Harris charts. The actual complex homomorphism on the real
algebra supplies a real skew unit h(i). The existing positivity
certificate gives a positive twist at that real unit. To obtain the
rational beta required by this statement, one needs openness of the
positive-twist condition in the real skew subspace and density of its
rational points, retaining invertibility. The published proof supplies
these steps as theorems rather than hypotheses. In the namespace
`Langlands.Shimura.AlgebraInvolution`,
`PositiveComplexHom.exists_skew_trace_pos` produces the real skew element,
`exists_rational_skew_trace_pos` selects a rational skew
element by openness and density, and
`exists_isPositive_skewAdjoint_of_trace_pos` proves that it
is a unit with positive conjugated involution. Its Markdown describes the
route, which proves openness directly for a skew trace form instead of
transcribing the positive-cone lemma. The statement does not assume any of
these steps.

## Use in the PEL construction

The starting Harris involution sigma already has the required group
signatures. The desired positive involution tau is an auxiliary left
algebra involution for the PEL model. If beta is a witness, gamma =
beta inverse is skew for tau and the gamma-conjugated involution of
tau is sigma. Thus the PEL form built using tau and gamma can retain
the original Harris right-adjoint group. That algebraic construction
and comparison are published separately: `Langlands.Shimura.PEL.PositiveInput`
builds the auxiliary algebra, its trace form and the similitude comparison
from any witness, and `Langlands.Shimura.PEL.HarrisPositiveInput` applies
them to the witness chosen from `positiveRationalSkewTwistExists`
(`harrisPositivePELUnit`, `harrisPositivePELAlgebra`, `harrisPositivePELForm`
and `harrisPositivePELSimilitudesEquiv`). The positivity in this target is
positivity of the auxiliary algebra involution, not the sign or positivity
of a Hodge polarization form. This target alone supplies none of those
constructions, nor scalar extension, lattices, adelic levels or the actual
moduli schemes.

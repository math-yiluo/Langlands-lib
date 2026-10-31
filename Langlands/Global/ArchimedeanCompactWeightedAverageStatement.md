# Weighted compact averaging in the actual derivative topology

Authors: Worker 94 and Worker 566. The Lean statement reuses Worker 94's
checked draft unchanged; Worker 566 checked the published interfaces and
original motivating passage and clarified the scope below.

`Langlands.Global.ArchimedeanGL.CompactWeightedAverageStatement K n` is
an internal analytic prerequisite for continuous compact-type projections.
It uses the published actual standard compact subgroup and
`DerivativeSmoothFunctions K n` with its full derivative compact-open
topology, for every number field in arbitrary universe and every natural
rank, including zero. The topology is the published topology induced by
`DerivativeSmoothFunctions.derivativeCoordinates` into the product, over
all `a : EnvelopingAlgebra K n`, of the compact-open spaces of continuous
functions on the actual group. The statement introduces no replacement
topology or action.

For every compatible Borel measurable-space structure on the actual
compact subgroup, every finite measure `ν`, and every continuous complex
weight `w`, the proposition asserts one continuous complex linear
endomorphism `A`. Its value at `f`, evaluated at any actual group element
`x`, is exactly

`∫ k, w(k) f(x k) dν(k)`.

The second clause puts `A f` in the topological closure of the complex
linear span of the actual compact right orbit of `f`, using the published
`DerivativeSmoothFunctions.compactAction K n` and
`Submodule.topologicalClosure` in that derivative topology. There is no
Haar, normalization or invariance hypothesis; the complex weight has no
positivity restriction, and the zero measure is included. Neither compact
finiteness, center finiteness nor analyticity is assumed. The scalar
integrands are continuous on a compact space, so their integrals are
genuine integrable scalar integrals.

This formulation separates integration in the actual derivative topology
from the later compact representation theory. The motivating source is
Harish-Chandra, *Discrete series for semisimple Lie groups II*, section 2,
printed/PDF page 8, where a normalized conjugate-character integral
defines a compact-type projection. The registered original is
`harish-chandra-1966-discrete-series-ii`, retained at
`/home/taskhub/pilot/literature/Harish-Chandra, Discrete series for semisimple Lie groups II- Explicit determination of the characters (1966).pdf`.
The arbitrary finite-measure statement and its orbit-closure clause are
internally derived prerequisites, not a transcription of that source.

Three obligations remain for a proof. First, the scalar formula must lift
to an actual smooth function for every input `f`, and these lifts must
form one complex linear operator `A` for the fixed measure and weight.
The published `Langlands.Analysis.compactLinearParameterIntegral` supplies
a scalar smoothness and first-derivative theorem for continuously varying
real linear maps; its specialization to actual matrix coordinates is
part of this smooth-lift obligation.

Second, the lifted operator must be continuous in the full derivative
topology. This requires continuity of
`f ↦ DerivativeSmoothFunctions.derivativeCLM K n a (A f)` in the
compact-open topology for every genuine enveloping element `a`, not just
continuity of scalar point evaluations. Derivative interchange and the
required compact-set estimates remain to be proved.

Third, each `A f` must belong to the closed complex linear span of the
actual compact right orbit of `f`, with closure in the same derivative
topology. Scalar integrability and pointwise smoothness alone do not
establish this clause. No completeness of the smooth-function space,
locally convex vector integral or projection is assumed as a certificate.

This file defines a proposition only. It asserts no character
orthogonality, algebraic isotypic range identification, idempotence,
equivariance, finite multiplicity, reproduction or automorphic
differential growth.

# Scalar-character occurrence in opposite Jacquet modules: proof

Author: Worker 99.

`Langlands.Exponents.refinedQuotientOppositeCharacter` proves exactly the
published `Langlands.Exponents.RefinedQuotientOppositeCharacterStatement`.
The field universe `uF`, inducing-carrier universe `uV` and quotient-carrier
universe `uW` remain independent. The theorem is closed and has no additional
parameters or hypotheses. It leaves the statement pair and its imports unchanged.

The proof imports
`Langlands.Representation.Parabolic.SecondAdjointnessProof` and uses the refined
clause of the published theorem
`Langlands.Parabolic.normalizedSecondAdjointness.{uF,uV,uW}`. Thus the
second-adjointness equivalence is supplied by a proof rather than assumed.
It relates the actual upper normalized refined induction to the actual
normalized opposite Jacquet quotient used in the target.

A surjective intertwiner onto a nontrivial carrier is nonzero: choose a nonzero
target vector and a preimage, and evaluate a hypothetical zero map there. The
complex-linear second-adjointness equivalence preserves nonzeroness. A nonzero
intertwiner is nonzero at some vector. Equivariance and scalar action on the
whole source make its image a nonzero eigenvector for the same character along
the same flattened scalar homomorphism. The existing
`isGeneralizedEigencharacter_of_eigenvector` provides one uniform power, namely
one, for the generalized-character space.

The opposite normalized Jacquet representation is smooth. An open subgroup
fixes the chosen eigenvector; its preimage along the scalar homomorphism lies
in the character kernel, since scalar multiplication on a nonzero vector is
injective in the scalar. A subgroup containing an open subgroup is open. The
scalar homomorphism is continuous coordinatewise by `scalarContinuous`, then
by `flattenedLeviEquivContinuous`; the required ring-topology instance comes
from the supplied field realization's module topology.

This is an internal derived linear-algebra and smoothness argument, with no
external citation. Its route is the one recorded in the target's paired
Markdown. The open-kernel pattern follows the private helper in
`Classification/SquareIntegrableCentralCharacterProof`, which was read for the
pattern. The local private lemma `eigenvector_open_kernel` implements that
argument here, without importing the classification proof. The only direct
imports are the target statement and the second-adjointness proof.

The proof uses smoothness of the opposite Jacquet module and does not assume
nontriviality of the inducing carrier. It applies to every refinement, including
the unrefined one, and arbitrary reducible admissible source and quotient. It
assumes no irreducibility, cuspidality, finite length, unitarity or analytic
criterion. The same character and scalar map occur in both the hypothesis and
conclusion. The conclusion is the existing uniform generalized-character
predicate, with the same exponent one for all scalar tuples.

The imported second-adjointness proof is assembled from natural induction
duality, natural Jacquet duality and first adjointness. Its dependency closure
uses none of the discrete-series positive-root or joint-support results,
regular-head existence or exhaustion, tempered exhaustion, square-integrable
Langlands classification or ordered-segment classification excluded by the
task. This proof supplies only scalar-character occurrence and openness of the
kernel. It makes no analytic transport, strict-cone, unitarity or classification
claim.

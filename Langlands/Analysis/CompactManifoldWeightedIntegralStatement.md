# Compact scalar kernels on manifolds with Banach-valued weights

Worker 116 states the internal target
`Langlands.Analysis.CompactManifoldWeightedIntegralStatement`.
This file contains a proposition definition and no proof.

Let `X` be a compact Hausdorff space with its Borel measurable structure and a
finite measure `μ`. Let `M` and `N` be real smooth manifolds with the specified
boundaryless models `V` and `H`, respectively. Let `E` be a complete complex
normed space, `w : C(X,E)` and `j : C(X,N)` be continuous, and
`h : M × N → ℂ` be jointly real smooth for the product of these specified models.
Then the target asserts:

1. For every `p : M`, `x ↦ h(p,j(x)) • w(x)` is Bochner integrable for `μ`.
2. The literal integral `p ↦ ∫ x, h(p,j(x)) • w(x) ∂μ` is real smooth as a map
   from the original manifold `M` to `E`.

The field of scalars for the smoothness conclusion is real, obtained on `E` by
restricting its complex scalar action. The six universes of `X`, `V`, `M`, `H`,
`N` and `E` are independent. Neither model is assumed finite dimensional or
complete. No second-countability, separability, invariant measure, group action,
nonempty source or nonzero measure assumption is imposed. The manifolds carry
exactly the supplied charts and topologies, rather than replacement spaces.
Compact Hausdorff is an explicit assumption on the integration source `X`; the
statement does not impose a manifold structure on it or require `j` to be smooth.

## Internal derivation and remaining proof

This is derived analytic infrastructure, with no external source transcription.
The existing public `contDiffOn_infty_compactFamily_of_joint` in
`Langlands/Analysis/CompactParameterSmoothness.lean` provides the coordinate-space
supremum-norm smoothness step. The published `compactWeightedIntegral` in
`Langlands/Analysis/CompactWeightedIntegral.lean` is the actual bounded map
integrating a scalar continuous function against a fixed vector-valued weight.
Its operator bound is `∫ x, ‖w(x)‖ ∂μ`.

The intended proof is local in the parameter manifold. In a parameter chart,
cover `j(X)` by finitely many chart sources of `N`. Their inverse images form an
open cover of compact Hausdorff `X`. A continuous finite partition of unity with
supports inside these open sets reduces the integral to finitely many compact
pieces. On the support of each weight, the corresponding chart composed with `j`
is continuous and takes values in its chart target. The jointly smooth kernel
written in the two charts gives a smooth scalar family in the supremum norm.
Compose with the bounded weighted-integral map, restricted to real scalars, and
sum the pieces. Bochner integrability follows separately from continuity on
compact `X` and finiteness of `μ`.

That description is a proof plan, not a proved theorem. The finite partition,
compact support restrictions, exact integral identity and chart-local smoothness
must all be established by a future exact-target proof. The statement imports no
unpublished theorem and assumes none of those conclusions as extra hypotheses.
In particular the unproved Euclidean weighted-parameter target is not a proof
input of this statement file.

## Application boundary

This target is intended for genuine compact families on the already constructed
manifold of infinite adelic points of a connected reductive group. It supplies
neither a compactly supported group convolution formula nor its change of
variables, a common compact integration domain near a parameter, smooth-vector
density or the Getz–Hahn section 6.1 tensor realization. Those remain distinct
construction and proof obligations. A continuous representation orbit may serve
as the vector weight on a compact integration domain; no smoothness of that
original vector is assumed here.

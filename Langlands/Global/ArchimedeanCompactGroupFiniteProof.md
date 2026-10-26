# Compact group orbit finiteness and differential finiteness

Author: Worker 116. Module:
`Langlands.Global.ArchimedeanCompactGroupFiniteProof`.

The theorem
`Langlands.Global.ArchimedeanGL.compactGroupFiniteDifferential` proves the
exact published `CompactGroupFiniteDifferentialStatement K n` for every
`K : Type u` with `[Field K] [NumberField K]` and every natural rank `n`,
including zero. It says that finite dimension of the complex span of the
actual compact-group right translates of a smooth function implies finite
dimension of its orbit under the genuine compact enveloping action.
The target is imported unchanged from
[`ArchimedeanCompactGroupFiniteStatement`](ArchimedeanCompactGroupFiniteStatement.md).

## Implemented argument

The imported theorem `compactTangentCurve`, from
[`ArchimedeanCompactTangentProof`](ArchimedeanCompactTangentProof.md), supplies
for every compact skew-adjoint direction `X` a curve `c` in
`standardInfiniteCompact K n` through the identity whose mixed matrix
derivative at zero is `realLieAlgebraToMatrix K n X`. Its construction uses
the matrix exponential of `t • X`, which is orthogonal at real infinite
places and unitary at complex infinite places, transported to the actual
completion-based compact subgroup. This file uses the resulting exact
`CompactTangentCurveStatement` as a proved input.

`compactCurve_right_deriv` composes the smooth coordinate extension with the
matrix curve g*c(t). The product rule gives tangent g*X, and the scalar chain
rule therefore identifies exactly `smoothDifferential K n X f` evaluated at g.
The curve is in the actual completion-based compact subgroup throughout;
the coordinate equivalence and units chart cancel on genuine invertible
matrices. Differentiability at zero suffices.

`compactCurve_differential_mem` works in the existing `SmoothFunctions`
carrier, which inherits the pointwise topology from the complex function
space as a submodule. This topology is Hausdorff and has continuous vector
space operations. Any finite-dimensional complex subspace S is therefore
closed. The difference quotients

```text
(t⁻¹ : ℂ) • (smoothRightAction (c t) f - f)
```

belong to S when it is compact-group invariant. The scalar derivative lemma
gives their pointwise convergence along the punctured neighborhood of zero
to the actual smooth function `smoothDifferential X f`. Convergence in the
inherited subtype topology follows, and closedness puts that derivative
in S. No assertion about differentiability in the stronger derivative
compact-open topology is made or needed.

`compactGenerator_preserves` extends real-direction preservation to the
complex tensor product by tensor induction. `compactEnveloping_preserves`
then uses algebra-adjoin induction: scalar operators, sums and compositions
preserve S. The order of composition is the published `envelopingAction_mul`
convention.

Finally S is the complex span of the actual compact-group orbit of f. Its
finite dimension is exactly the given hypothesis, and its invariance is
`FiniteVectors.orbitSubrepresentation`. The tangent-curve theorem gives preservation
by each real compact generator. The compact enveloping orbit is consequently
a subspace of S and is finite-dimensional. No ambient finite-dimensionality,
connectedness, positive-rank, center-finiteness or growth hypothesis is used.
The argument is uniform in the universe, number field and every natural rank,
including zero.
`compactGroupFiniteDifferential_of_curves` records the reduction with the
curve statement as a premise. The final theorem discharges that premise
using `compactTangentCurve`. The final Lean example checks the entire
universe and parameter telescope of the unconditional theorem.

## Provenance and scope

This is an internal derived proof of the published target, developed by
Worker 116 from its actual definitions and Mathlib's chain-rule, topology,
finite-dimension and algebra-generation lemmas, using Worker 459's published
compact tangent-curve theorem. It does not attribute the matrix-specialized
argument to an original source. The motivating literature and its scope are
documented by the immutable target's Markdown.

No derivative invariance or compact tangent-curve hypothesis remains in the
final theorem. The simultaneous center condition, joint finiteness,
reproduction and the automorphic derivative-growth theorem remain separate
obligations.

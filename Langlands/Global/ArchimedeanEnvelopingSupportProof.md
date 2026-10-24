# Locality of the genuine archimedean enveloping action

`Langlands.Global.ArchimedeanGL.envelopingSupport` proves the published
`EnvelopingSupportStatement K n` in
`Langlands.Global.ArchimedeanEnvelopingSupportStatement`. For every
`(K : Type u) [Field K] [NumberField K]`, every natural rank `n`, every element
`a : EnvelopingAlgebra K n`, and every `f : SmoothFunctions K n`, it gives
`tsupport (envelopingAction K n a f).val ⊆ tsupport f.val`. The action is the
published genuine differential action, and topological support is the closure
of the nonzero set. There are no additional hypotheses, including when `n = 0`.
The same module proves its compact-support consequence,
`Langlands.Global.ArchimedeanGL.envelopingCompactSupport`.

The real-generator lemma transports eventual equality to zero at a point
outside the original topological support through the inverse open units chart
and the completion-coordinate homeomorphism. The coordinate extension is
therefore zero near the corresponding invertible matrix. Equality of the
Fréchet derivatives of locally equal functions makes its derivative zero, so
evaluation in the genuine matrix direction `gX` is zero. Taking closures of
supports yields topological-support containment.

Tensor-product induction extends the inclusion from real generators to the
complexified Lie algebra: scalar multiplication does not enlarge support and
the support of a sum is contained in the union. Lifting an enveloping element
to the tensor algebra then proves the same inclusion by induction on scalars,
generators, addition and multiplication. For multiplication, apply the first
operator's inclusion to the output of the second, and compose the two
inclusions. The compact-support theorem applies the statement module's closed
subset implication. All universes and ranks are unchanged; no automorphic
hypotheses are used.

This is an internal locality proof derived from the published concrete
operators and Mathlib's derivative-locality and algebra-induction results.
The implementation reuses Worker 94's proof draft; Worker 88 checked it against
the independently published statement and prepared the paired submission.
It supplies the support-preservation prerequisite for later smoothing arguments.
Existence of reproducing kernels, differentiation under the integral, and the
final automorphic differential-growth theorem remain separate obligations.

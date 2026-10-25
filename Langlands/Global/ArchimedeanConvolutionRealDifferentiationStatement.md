# Smooth compact convolution and real-generator differentiation

`Langlands.Global.ArchimedeanGL.CompactKernelConvolutionRealDifferentiationStatement`
defines a proposition, with no proof of its content in this module. Its complete
parameters are `(K : Type u) [Field K] [NumberField K] (n : ℕ)`, and its result is
`Prop`. Every natural rank is included, including zero. The module imports
`Langlands.Global.ArchimedeanConvolution` and uses its existing group, topology,
smooth functions, compact kernels, integral and differential operators.

## Exact assertion

For every `[MeasurableSpace (InfiniteAdelicGL K n)]` and compatible
`[BorelSpace (InfiniteAdelicGL K n)]`, every
`μ : Measure (InfiniteAdelicGL K n)` with `[IsFiniteMeasureOnCompacts μ]`,
every continuous complex function `f : C(InfiniteAdelicGL K n, ℂ)` and every
`κ : SmoothCompactKernel K n`, there exists one `F : SmoothFunctions K n`
such that

```text
F.val = rawConvolution K n μ f κ
```

and, for all `X : RealLieAlgebra K n` and `g : InfiniteAdelicGL K n`,

```text
(smoothDifferential K n X F).val g
  = ∫ y, f y * (smoothDifferential K n X κ.val).val (y⁻¹ * g) ∂μ.
```

Thus the underlying smooth function is exactly the raw right convolution
`g ↦ ∫ y, f y * κ.val.val (y⁻¹ * g) ∂μ`. The integrals are complex Bochner
integrals. The smooth lift is unique as an element of the published subtype
`SmoothFunctions K n`, although uniqueness is not an additional conjunct.
The same lift satisfies the derivative identity for every real generator.
There is no Haar invariance, nonzero-measure, positive-rank, global boundedness,
global integrability, input smoothness or reproduction premise. In particular
the zero measure and arbitrary continuous inputs are covered.

## Direction and local analytic provenance

The published `smoothDifferential_apply` evaluates the real Fréchet derivative
in matrix coordinates in the direction `gX`, with `g` and `X` interpreted via
`archimedeanGLCoordinates` and `realLieAlgebraToMatrix`. For fixed `y`, the
differential of left translation `g ↦ y⁻¹ * g` carries this direction to
`y⁻¹(gX) = (y⁻¹g)X`. Consequently the derivative on the kernel is the same
`smoothDifferential K n X`, with no sign, antipode or adjoint conjugation.
`envelopingAction_real_generator` identifies this operator with the action of
the enveloping generator associated to `complexify K n X`.

This is an internal local analytic prerequisite. The intended analytic argument
works in the published real matrix charts. If `g` ranges over a neighborhood
with compact closure `C` and `S` is the compact topological support of the
kernel, then `κ(y⁻¹g) ≠ 0` implies `y ∈ C * S⁻¹`. This is a fixed compact
integration region. The continuous input is bounded on that region and the
measure is finite there. Local bounds for the smooth kernel derivatives then
permit parameter differentiation under the integral, without a change of
integration variable or measure invariance. Smoothness of all orders and the
displayed generator identity remain to be proved; this paragraph describes
their analytic rationale.

## Relation to the full differentiation target

This statement restricts the derivative-transfer clause of
`CompactKernelConvolutionDifferentiationStatement` in
`Langlands.Global.ArchimedeanConvolutionDifferentiationStatement` to real Lie
generators. Its smoothness conclusion and every other hypothesis are unchanged.
It is weaker only in this restriction. It does not by itself constitute a proof
of the full enveloping target.

The algebraic extension still requires complexification and enveloping
induction, with composition in the published order
`D(a * b) = D(a) ∘ D(b)`. Compact support of differentiated kernels and the
integral linearity steps use the separate published support results
`Langlands.Global.ArchimedeanGL.envelopingSupport` and
`Langlands.Global.ArchimedeanGL.envelopingCompactSupport` in
`Langlands.Global.ArchimedeanEnvelopingSupportProof`.
The present statement has no separate differentiated-integrand integrability
conjunct. That integrability follows from support preservation and the
continuous compact-support argument used by `convolution_integrable`.
No reproduction or automorphic differential-growth theorem is asserted here.

The motivating source is Borel–Jacquet, *Automorphic forms and automorphic
representations* (1979), §2.2, printed p.193 / one-based PDF p.188 of Corvallis
Part I, registered as `borel-jacquet-1979-automorphic`, SHA256
`3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
That passage uses compact smooth reproducing convolution to obtain derivative
growth. The arbitrary-measure local analytic formulation here is internal,
not a verbatim theorem of that source. The cited original page was read for
this statement; no source-specific project erratum was found. The existing
[full-target rationale](ArchimedeanConvolutionDifferentiationStatement.md) and
[source map](../../notes/automorphic/differential-growth-source-map.md) explain
the surrounding proof obligations.

The Lean example checks the complete parameter shape and `Prop` result; it
proves none of the proposition's analytic content.

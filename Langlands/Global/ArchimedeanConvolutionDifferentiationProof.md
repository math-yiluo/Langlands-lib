# Smooth compact convolution and enveloping differentiation

`Langlands.Global.ArchimedeanGL.compactKernelConvolutionDifferentiation`
proves the entire published proposition
`Langlands.Global.ArchimedeanGL.CompactKernelConvolutionDifferentiationStatement K n`.
Its parameters are `(K : Type u) [Field K] [NumberField K] (n : ℕ)`, with no
additional hypothesis.

For every Borel-compatible measurable structure on the actual completion-based
group `InfiniteAdelicGL K n`, measure `μ` finite on compact sets, continuous
complex function `f`, and smooth compact kernel `κ`, it constructs a single
`F : SmoothFunctions K n` with

```text
F.val = rawConvolution K n μ f κ
```

and, for every `a : EnvelopingAlgebra K n` and group element `g`,

```text
(envelopingAction K n a F).val g
  = ∫ y, f y * (envelopingAction K n a κ.val).val (y⁻¹ * g) ∂μ.
```

The proof retains every natural rank, including zero. Neither invariance nor
nonvanishing of the measure, smoothness or global boundedness of `f`, nor a
reproduction identity is required. The group, smooth-function subtype,
convolution integral, complexified Lie algebra and enveloping action are the
existing Library constructions.

## Analytic input

The imported theorem `compactKernelConvolutionRealDifferentiation` from
`Langlands.Global.ArchimedeanConvolutionRealDifferentiationProof` proves the
published `CompactKernelConvolutionRealDifferentiationStatement K n` without
additional premises. It constructs the smooth lift of the actual raw integral
and transfers each real generator to the kernel.

That proof chooses a fixed compact integration region on a neighborhood of
each output point, applies the published compact linear-parameter integral
theorem in the real matrix coordinates of the units group, and identifies the
actual differential. Its direction at `g` is `gX`; left multiplication by
`y⁻¹` sends this to `(y⁻¹g)X`. Thus the real-generator formula has the
convention needed here, with no sign, antipode or adjoint. The analytic proof
also uses the published support-locality result to recover a full-group
integral after differentiation.

## Extension to the complexified enveloping algebra

`compactKernelConvolutionDifferentiation_of_real` is a separate conditional
lemma: its sole mathematical premise is the whole real-generator statement.
For fixed `μ` and `f`, classical choice selects a smooth lift `S η` for every
compact kernel `η`. The identities `hS` and `hD` record its underlying raw
convolution and its real-generator transfer.

The local assertion `hI` proves integrability of every enveloping-derivative
integrand. It packages `envelopingAction K n a η.val` as a compact kernel
using the published `envelopingCompactSupport`, and applies the existing
`convolution_integrable`. The assertion `hJ` specializes this to a complex
Lie generator using `envelopingAction_generator`.

Tensor-product induction proves `hC`, transfer for each element of
`ComplexLieAlgebra K n`. On a pure tensor `z ⊗ X`, the published action is
`z` times the real action, so complex scalar multiplication commutes with the
Bochner integral and `hD` applies. For a sum, `hJ` supplies the two
integrability hypotheses required by `integral_add`.

For an arbitrary enveloping element, surjectivity of the defining ring
quotient supplies a representative in the tensor algebra. Tensor-algebra
induction then proves `hA`:

- Scalars act by scalar multiplication; the integral formula follows from
  `hS` and `integral_const_mul`.
- A generator is the complex Lie algebra case `hC`.
- Addition uses linearity of the action and `integral_add`, with integrability
  supplied by `hI`.
- For a product represented by `x * y`, let `b` be the enveloping image of
  `y` and let `ηb` be the compact kernel obtained by applying `b` to `η`.
  The induction hypothesis for `y` and the identity `hS ηb` show pointwise
  that `envelopingAction K n b (S η) = S ηb`. Subtype extensionality turns
  this into equality of smooth functions. The algebra-homomorphism identity
  for the action rewrites the product as composition, and the induction
  hypothesis for `x`, applied to `ηb`, gives the required integral.

This multiplication step uses exactly the existing convention
`D(a * b) = D(a) ∘ D(b)` and preserves its order. Choosing `S κ` yields one
smooth lift valid for all enveloping elements. The unconditional exported
theorem applies this conditional lemma to the imported analytic theorem.

## Provenance and scope

This is an internal algebraic derivation from the published real-generator
convolution theorem, compact-support preservation, the actual complexified
enveloping action, and Bochner integral linearity. The concrete analytic
argument is contained in the imported proof and its paired Markdown; the
present module supplies complexification and enveloping induction. It leaves
the target statement and its imported definitions unchanged.

The result proves smoothing and derivative transfer. Reproduction and
automorphic differential growth remain separate statements.

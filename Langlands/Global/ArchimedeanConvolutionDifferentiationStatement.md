# Smoothness and enveloping differentiation of actual right convolution

`Langlands.Global.ArchimedeanGL.CompactKernelConvolutionDifferentiationStatement`
is a proposition defining one analytic proof obligation. It is not proved in
this module. The parameters are every `K : Type u` with `[Field K] [NumberField K]`
and every `n : ℕ`, including zero.

## Exact assertion

Use the completion-based group `InfiniteAdelicGL K n`, its existing topology,
the genuine `SmoothFunctions K n` and `envelopingAction K n`, and the published
compact smooth kernel space and raw integral from `ArchimedeanConvolution`.
For any measurable structure compatible with that topology's Borel sets and
any measure `μ` finite on compact sets, the statement quantifies over:

- An arbitrary continuous complex function `f` on the group.
- An actual smooth compact kernel `κ : SmoothCompactKernel K n`.

It asserts that there exists `F : SmoothFunctions K n` whose underlying function
is exactly

```text
F(g) = rawConvolution K n μ f κ g
     = ∫ y, f(y) κ(y⁻¹ g) dμ(y),
```

and, for every element `a` of the actual complex enveloping algebra and every
group element `g`,

```text
(D(a)F)(g) = ∫ y, f(y) (D(a)κ)(y⁻¹ g) dμ(y).
```

Here `D(a)` denotes the published `envelopingAction K n a`. The kernel is
differentiated as `κ.val : SmoothFunctions K n`; its underlying function is
`κ.val.val`. The integrals are Mathlib's complex Bochner integrals.
The equality of underlying functions fixes the smooth lift uniquely because
`SmoothFunctions` is a subtype of functions. No new carrier, differential
operator, or regularity assumption is introduced.

Only Borel compatibility and finiteness on compact sets are required of `μ`.
The target therefore specializes to the constructed left Haar measure. It also
includes the zero measure. Neither global integrability nor boundedness nor
smoothness of `f` is a premise. The kernel need not reproduce `f`.

## Differential convention and scope

The real generator acts at `g` in the direction `g X`, as specified by
`envelopingAction_real_generator_apply`. Thus fixing `y` and differentiating
`κ(y⁻¹ g)` transfers that same differential to `κ`: the translated direction is
`(y⁻¹ g) X`. Iteration respects the multiplication convention
`D(a * b) = D(a) ∘ D(b)`. The displayed formula has neither a sign nor an
antipode nor an adjoint conjugation of `a`. This explains the intended
convention; it is not a proof of differentiation under the integral.

The already published `convolution_integrable` establishes integrability of the
undifferentiated integrand. This statement does not separately assert
integrability of each differentiated integrand. Compact-support preservation
by the enveloping action is the separate
`EnvelopingSupportStatement` obligation; once proved, it supplies that
integrability by the same continuous compact-support argument.
Proving the present target still requires local uniform compact support and
differentiation under the integral, including arbitrary orders.

This unit supplies no reproducing-kernel theorem, derivative compact-open
topology, approximation theorem, or automorphic polynomial-growth proof.
Those remain independent obligations. The example in the Lean file checks the
complete parameter shape of the proposition and proves none of its content.

## Provenance

This is an internal analytic statement formulated against the published
concrete definitions. It isolates the smoothing and derivative-transfer step
needed by Borel–Jacquet, *Automorphic forms and automorphic representations*
(1979), §2.2, printed p.193 / PDF p.188 of Corvallis Part I, registered as
`borel-jacquet-1979-automorphic`, SHA256
`3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
The original passage motivates compact smooth reproduction and derivative
growth; the explicit measure-generic formulation here is internal, not a
verbatim assertion from that source. Its applicability without Haar invariance
comes from the intended local parameter-integral argument, not from importing
the source's stronger reproduction conclusion as a hypothesis. The source was
read in the parent source audit; no applicable project erratum was found.

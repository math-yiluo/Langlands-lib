# Proof that the integrated action turns convolution into composition

The theorem `Langlands.Analysis.integratedActionConvolution` proves the
published proposition `Langlands.Analysis.IntegratedActionConvolutionStatement`
(module `Langlands.Representation.Unitary.IntegratedConvolutionStatement`)
at the two independent universes `uG` of the group and `uE` of the Banach
space. The original measure, representation and weights are kept as they are.

## Provenance

The argument is internal: it uses the shear, Fubini and left invariance, as
outlined in the statement's Markdown. It does not transcribe a literature
proof. The statement's Markdown cites Getz–Hahn, *An Introduction to
Automorphic Representations*, section 3.4, formula (3.9) and Exercise 3.20,
for the right-measure version of the identity; this proof neither uses nor
formalizes that version.

## Proof

Write `K(a, g) = f₁(a) f₂(a⁻¹ g)` on `G × G` with the product measure
`μ × μ`, and let `S(a, b) = (a, a b)` be the shear.

1. **The kernel is integrable.** Mathlib's `measurePreserving_prod_mul`
   shows that `S` preserves `μ × μ` for a left invariant s-finite `μ`, and
   `MeasurableEquiv.shearMulRight` makes it a measurable embedding. By
   `MeasurePreserving.integrable_comp_emb`, `K` is integrable if and only if
   `K ∘ S` is. Since `K(a, a b) = f₁(a) f₂(b)` (by `inv_mul_cancel_left`),
   `Integrable.mul_prod` gives integrability of `K ∘ S`.
2. **The convolution is integrable.** `Integrable.integral_prod_right`
   applied to `K` gives integrability of `g ↦ ∫ a, K(a, g)`, which is the
   convolution `f₁ ⋆ f₂`. This is the integrability proof used in the
   existential conclusion.
3. **The vector kernel is integrable.** The function
   `(a, g) ↦ K(a, g) • π g x` is almost everywhere strongly measurable,
   since `K` is and the orbit composed with the second projection is
   (`AEStronglyMeasurable.comp_snd`). Its norm equals `‖K(a, g)‖ ‖x‖`
   because `π g` preserves norms, so it is dominated by an integrable
   function.
4. **Inner integral.** For fixed `a`, left invariance
   (`integral_mul_left_eq_self`) substitutes `g = a b`. Then
   `K(a, a b) • π(a b) x = f₁(a) • π(a) (f₂(b) • π(b) x)`, using that `π` is a
   homomorphism and `π(a)` is linear. Pulling out the scalar
   (`integral_smul`) and the bounded operator `π(a)`
   (`ContinuousLinearMap.integral_comp_comm`, with the published
   `isometricActionIntegrand_integrable` for `f₂`) gives
   `∫ g, K(a, g) • π g x = f₁(a) • π(a) (π(f₂) x)`.
5. **Assembly.** By the published `integratedIsometricAction_apply`, the
   left side is `∫ g, (∫ a, K(a, g)) • π g x`. `integral_smul_const` moves the
   vector inside the inner integral, `integral_integral_swap` (Fubini, from
   step 3) exchanges the integrals, and step 4 identifies the result with
   `∫ a, f₁(a) • π(a) (π(f₂) x) = π(f₁) (π(f₂) x)`.

The proof uses Mathlib and the published `IntegratedOperator` module only.

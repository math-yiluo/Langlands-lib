# Compact-support changes of variables and the right Hecke action

Worker 133, Task 5403. Internal supporting lemmas for Renard III.2.6,
printed pp.75–76 / PDF pp.81–82 in the registered French 9 July 2026 source
`renard-2026-representations-groupes-reductifs-padiques`.

The internal definition `Homomorphism.rightConvolutionKernel` packages the
subgroup test function b(h)=ΔG(φ(h))a(h)f(xφ(h)⁻¹). Its local constancy and compact
support let the existing algebraic action be compared with its scalar integral.
This is a derived auxiliary construction for the published right action,
rather than an additional assertion attributed to Renard.

The right-translation integral identity uses Mathlib's uniqueness of Haar
integration on continuous compactly supported functions, applied separately to
the real and imaginary parts. The scalar factor is the modular character by
Mathlib's right-pushforward characterization. Complex continuous linear maps
commute with the integral to reassemble the identity. This retains arbitrary
supplied Haar measures without a regularity or countability hypothesis.

For inversion, choose a normalized compact-open indicator e of integral one.
The continuous kernels f(x)e(yx) and f(y⁻¹z)e(z) have compact support: their
supports lie in products built from the compact supports of f and e. Two
compact-support Fubini swaps and left-Haar substitution show
∫ f(x⁻¹) = ∫ f(x)Δ(x). Applying this to the inverse test function proves
that the integral is preserved by the existing `haarInversion`.

The right module calculation expands the published definition using
`leftModule_apply`. The two ambient modular factors at x and x⁻¹ cancel.
The remaining integrand is the weighted inverse of the subgroup test function
b(h)=ΔG(φ(h))a(h)f(xφ(h)⁻¹). It has compact support because a does, and is
locally constant by continuity of φ and local constancy of the modular
character. Weighted inversion therefore gives the claimed integral formula
for the original right module, for any continuous homomorphism φ.

Mathlib's modular character Δ, named `haarScale`, is the inverse of Renard's
modular function. These are supporting lemmas; the natural compact-induction
tensor isomorphism is still a separate obligation.

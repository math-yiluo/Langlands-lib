# Scalar extension of the actual tangent Lie algebra over a field

Let `k` be a field and let `G` be a group scheme over `Spec k` whose structure
map is affine and locally of finite type. Let `A` be any commutative
`k`-algebra. The published module `ScalarExtension.lean` constructs the
`A`-linear isomorphism

`kernelScalarExtension G A : A ⊗[k] Additive (lieKernel G k) ≃ₗ[A] Additive (lieKernel G A)`

between the scalar extension of the tangent space at the identity and the
actual dual-number kernel of `G` with coefficients in `A`. On pure tensors it
sends `a ⊗ x` to `a • lieKernelMapLinear G (Algebra.ofId k A) x`
(`kernelScalarExtension_tmul`).

This module shows that this isomorphism also preserves the Lie bracket.

- `kernelScalarExtension_lie`: for all `x, y` in `A ⊗[k] Additive (lieKernel G k)`,
  `kernelScalarExtension G A ⁅x, y⁆ = ⁅kernelScalarExtension G A x, kernelScalarExtension G A y⁆`.
  On the source the bracket is Mathlib's extended-scalars bracket
  (`LieAlgebra.ExtendScalars`, with `⁅a ⊗ x, b ⊗ y⁆ = (a * b) ⊗ ⁅x, y⁆`). On the
  target it is the published convolution bracket on the actual tangent module
  over `A` (`AffineBracket.lean`).
- `kernelScalarExtensionLieEquiv G A`: the same map bundled as an isomorphism
  of Lie algebras over `A`,
  `A ⊗[k] Additive (lieKernel G k) ≃ₗ⁅A⁆ Additive (lieKernel G A)`. The lemmas
  `kernelScalarExtensionLieEquiv_apply`,
  `kernelScalarExtensionLieEquiv_toLinearEquiv` and
  `kernelScalarExtensionLieEquiv_tmul` record that its underlying map is
  `kernelScalarExtension G A`.

**Proof.** Both brackets are additive in each variable, so tensor induction on
`x` and then on `y` reduces the claim to pure tensors `a ⊗ x` and `b ⊗ y`. For
these, the source bracket is `(a * b) ⊗ ⁅x, y⁆`, which maps to
`(a * b) • lieKernelMapLinear G (Algebra.ofId k A) ⁅x, y⁆`. The published
`lieKernelMapLinear_lie` (`AffineBracketFunctoriality.lean`) says that
coefficient change preserves the bracket. The target bracket is `A`-bilinear,
so `⁅a • X, b • Y⁆ = (a * b) • ⁅X, Y⁆`, and the two sides agree.

**Instances.** The published instances `Lie.instAffineKernelLieRing` and
`Lie.instAffineKernelLieAlgebra` are stated for algebras over a bundled ring
`R`. Instance search does not find them for a `k`-algebra `B` regarded as an
algebra over `CommRingCat.of k`. The module therefore declares two local
instances, `instKernelLieRingOfField` and `instKernelLieAlgebraOfField`, which
are these published instances specialised to `R := CommRingCat.of k`. They add
no new structure.

## Source and scope

Milne, *Algebraic Groups* (2017 and 2022 corrected reprint), 10.18–10.19,
printed pp.191–192. For a finitely generated commutative `k`-algebra `R`,
Milne defines `g(R) = Ker(G(R[ε]) → G(R))` and proves `g(R) ≅ g ⊗ R`,
functorially in `G` (equation (59)). Milne uses this identification
throughout §10d to define the adjoint representation and the bracket. This
module adds, as a derived result, the statement that the identification is an
isomorphism of Lie algebras. On `g(R)` the bracket is the actual convolution bracket at the
test algebra `R`; on `g ⊗ R` it is the bracket extended from `g`. The result
holds for every commutative `k`-algebra, not only finitely generated ones,
because `kernelScalarExtension` does. Neither errata snapshot (2017, 2 November
2026; 2022 reprint, 4 November 2026) has an entry for pp.191–192.

This module does not treat base change of the group scheme `G` itself. It does
not compare `lieKernel G A` with the tangent space of a base-changed group
`G_A`. It does not discuss naturality in `G`; the linear naturality
`targetMapLinear_kernelScalarExtension` is published in
`SurjectiveDifferentialLifting.lean`.

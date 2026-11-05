# Scalar extension of the actual smooth affine Lie module

Let `G` be a smooth affine group scheme over `Spec R`, for any commutative
ring `R`. For every commutative `R`-algebra `A`,
`smoothKernelScalarExtension` identifies
`A ⊗[R] Additive (lieKernel G R)` with the actual dual-number identity
kernel `Additive (lieKernel G A)`. Its simple-tensor formula is the
actual coefficient change followed by scalar multiplication:
`a ⊗ X` maps to `a • lieKernelMapLinear G (Algebra.ofId R A) X`.
In particular, the equivalence is tied to the given group and its actual
points on test algebras.

The proof uses the actual identity cotangent module and its finite
projectivity from `Lie.SmoothFiniteProjective`. The cotangent universal
property, expressed by `identityCotangentHomEquiv`, identifies maps from
this module into `A` with coordinate derivations at the identity.
For a finite projective module, Mathlib's `dualTensorHomEquiv` is an
equivalence. Tensor symmetry and the actual cotangent-dual identification
therefore give an `R`-linear equivalence on identity derivations.

The implemented proof compares this equivalence to the natural
`A`-linear tensor map on actual identity derivations, by evaluating on
simple tensors and differentials of coordinate elements. It follows
that the natural map is bijective. Transport through the published
actual-kernel derivation equivalences supplies the asserted `A`-linear
Lie-module equivalence and its formula.

The provenance is internal: this extends the existing field-only
derivation tensor argument using finite projectivity of the actual
smooth identity cotangent module. It assumes no flatness of the
test algebra `A`, no chosen basis, and no field or noetherian hypothesis
on `R`. Comparison with the Lie module of a group after scheme base
change, and relative adjoint-weight compatibility, are separate
constructions.

# The adjoint representation on dual-number kernels

This module bundles conjugation on the actual identity kernel as a linear
representation, using `Lie.AffinePoints`, `lieKernel`, and the module structure
from `Lie.AffineModule`.

The source is Milne, *Algebraic Groups* (2017), §§10.18–10.20, printed
pp.191–192 (PDF207–208). Milne defines the action by conjugation after the
constant inclusion into dual-number points. The extension to affine group
schemes over arbitrary commutative base rings, with unrestricted commutative
test algebras, is derived; no finite-type or smoothness assumption is used.

`lieKernelConjugationLinear` has the previously defined actual conjugation as
its underlying map. Additivity follows from its group-homomorphism law;
linearity follows from its proved compatibility with epsilon scaling.
`adjoint G A` bundles these endomorphisms as a monoid homomorphism. The identity
and multiplication laws follow from the constant-point homomorphism and the
group laws, preserving the orientation `ι(g) x ι(g)⁻¹`.

`adjoint_val` states that formula on the actual scheme points.
`adjoint_naturality` identifies the two composites with the semilinear
coefficient-change map for every algebra homomorphism `A →ₐ[R] B`; it follows
from the previously proved naturality of actual conjugation.

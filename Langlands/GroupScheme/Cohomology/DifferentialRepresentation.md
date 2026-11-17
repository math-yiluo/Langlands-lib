# Natural module representations from actual differential actions

Let `a` be an actual automorphic action of a group scheme `H` on a smooth affine group scheme `U` over `Spec R`. The Library already constructs the differential action of each `H(A)` on the actual dual-number Lie module of `U` over every affine test algebra `A`, and a canonical scalar-extension comparison from `A ⊗[R] Additive(lieKernel U R)` to that Lie module.

`smoothKernelScalarExtension_naturality` proves that this comparison commutes with every change of affine test algebra. The proof uses tensor induction. On a pure tensor, the published formula for scalar extension expresses it as an epsilon scaling of the extended base Lie point. Passing to identity derivations, coefficient naturality and the algebra-homomorphism multiplication and structure-map laws identify the two expressions.

`differentialTensorAction` transfers the actual differential representation across these linear equivalences. Its value on a point is the scalar-extension comparison, followed by that point's differential action, followed by the inverse comparison. The identity and product laws follow from those of the published differential representation.

`differentialModuleRepresentation` packages these actions as `ModuleRepresentation (Additive(lieKernel U R)) H`, including naturality under every algebra homomorphism. Its naturality proof combines the scalar-extension comparison just proved with the published naturality of the differential action.

`adjointModuleRepresentation G` specializes to conjugation of a smooth affine group `G` on itself. It therefore gives the actual quasi-coherent adjoint module action in the regular-cochain interface. There is no affineness or smoothness assumption on the acting group `H` in the general construction.

This module does not identify conjugation on arbitrary square-zero reduction kernels with this tensor-valued adjoint representation. It also constructs no nonaffine Lie-coefficient representation and proves no cohomology vanishing or homomorphism lifting theorem.

This is an internal derived construction from the published actual differential action, smooth affine Lie scalar-extension comparison and coordinate-derivation naturality, together with the regular-cochain module interface. It introduces no new literature assertion.

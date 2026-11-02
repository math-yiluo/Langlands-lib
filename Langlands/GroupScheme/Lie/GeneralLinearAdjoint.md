# Linear GL_n Lie coordinates and the adjoint formula

This module extends the published `GeneralLinear.DualNumber` comparison without
changing its carrier or its coordinate map. The source is Milne, *Algebraic
Groups* (2017), §§10.11, 10.18–10.20, printed pp.189,191–192 (PDF205,207–208).
The arbitrary commutative base ring, arbitrary commutative test algebra, and
explicit bridge to the Library's actual scheme-point coordinates are derived.

`pointKernelLinearEquiv` is the existing `pointKernelEquiv`, followed by the
additive alias of the same kernel. It is linear because the published addition
formula is exactly the kernel's group law, and the published epsilon-scaling
formula is exactly its scalar multiplication. Its inverse is the published
coefficient recovery. `pointKernelLinearEquiv_naturality` gives compatibility
with every coefficient-algebra homomorphism.

The imported `MatrixRepresentationDifferentialConjugation` module supplies
`constantMatrix_mul_epsilonMatrix`, `epsilonMatrix_mul_constantMatrix` and
`matrixUnit_conjugate`. Its entrywise dual-number calculations give the constant
identity term and epsilon coefficient `gXg⁻¹`. `matrixUnit_conjugation` is the
symmetric orientation of that published conjugation theorem.
`pointUnit_conjugation` transports this identity through the published natural
multiplicative affine-point equivalence. `adjoint_pointKernelLinearEquiv`
therefore identifies the actual adjoint action with matrix conjugation.

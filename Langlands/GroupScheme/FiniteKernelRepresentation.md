# A finite representation retaining the full kernel equations

`kernelDetectingRepresentation q` chooses one actual finite-dimensional
representation of the affine target of `q`, over an arbitrary field, when
the source scheme is Noetherian. It returns a dimension, an actual
homomorphism `ρ : Q → GL_n`, and a detection property: for every actual
homomorphism `r : H → G`, if `r ≫ q ≫ ρ` is trivial then `r ≫ q` is trivial.
In particular this applies to full scheme kernels; no affine-source or
reduced-source premise is introduced.

The construction first chooses the finite augmentation functions supplied by
`finiteKernelDetector q`, which generate the exact ideal sheaf of the full
kernel. Then `finiteFunctionsRepresentation` supplies one actual finite
representation whose pullback contains these functions. A homomorphism killed
by the represented composite therefore kills each detector function: counit
compatibility makes its value at the target identity zero. Pullback of the
finite ideal-sheaf equality implies that it factors through the full kernel
of `q`. The actual kernel square then makes its composite with `q` trivial.
The two supporting detector lemmas implement this argument.

The provenance is a derived finite-representation implementation of the
kernel-stabilization step in SGA 3, Exposé VI_B, Corollary 11.18.1 (printed
p.427 / PDF p.97), supporting Theorem 12.2(i). The registered source is
`sga3-expose-vib-gille-polo-2024`, Gille–Polo recomposed edition of 13 October
2024, SHA-256
`88d8ccb045fc959535155eb4b0fc72e3e4845730fb73355f2043e8023b7db3d2`.
This result does not assert that the affine target or the source is of finite
type; those conclusions are separate geometric steps.

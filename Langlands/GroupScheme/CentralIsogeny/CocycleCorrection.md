# Correction of a natural cocycle by a central kernel cocycle

`Cocycle.kernelCorrection` takes a cochain in the source group whose image trivializes the projected cocycle. Twisting by that cochain yields a natural cocycle with values in the scheme-theoretic kernel. The kernel point factorization gives the lifted natural cocycle and identifies its image with the twist.

`Cocycle.divCentral` divides a cocycle by the image of a cocycle along a central homomorphism. Centrality on all test schemes permits pointwise division to preserve the cocycle law. The difference is a coboundary if the two input cocycles are cohomologous in the source group. If the correction is in the kernel, projection of the difference has the same values as projection of the original cocycle. The pullback adjunction shows that this division commutes with base change on cocycle values. These are internal operations for the adjoint arithmetic reduction.

# Finite functions detecting the full kernel

`FiniteKernelDetector q` records finitely many global functions on the affine
target, each vanishing on its identity section, whose pullbacks generate the
exact ideal sheaf of the actual scheme-theoretic kernel of `q`.
`finiteKernelDetector q` constructs this data when the source scheme is
Noetherian and the target affine, over an arbitrary field. The source is not
assumed affine, smooth, connected or reduced.

The actual kernel square identifies its closed immersion ideal with pullback
of the target identity ideal. Since the target is affine, that ideal is the
ideal sheaf associated to the kernel of the identity section's map on global
functions. The published `comap_ofIdealTopFLT` identifies its pullback. Express
the augmentation ideal as the sum of its principal ideals and apply
`NoetherianIdealSheaf.finiteSupSupport` to their pulled-back ideal sheaves.
The resulting finite set gives equality of ideal sheaves, preserving all
nilpotent structure of the full kernel.

This is internal supporting mathematics for the finite kernel-control step
in SGA 3, Exposé VI_B, Corollary 11.18.1 (printed p.427 / PDF p.97), used by
Theorem 12.2(i) (printed p.430 / PDF p.100), Gille–Polo recomposed edition of
13 October 2024. The source identifier is `sga3-expose-vib-gille-polo-2024`,
SHA-256 `88d8ccb045fc959535155eb4b0fc72e3e4845730fb73355f2043e8023b7db3d2`.
The construction uses the current actual group kernel and scheme ideal-sheaf
APIs; it does not supply faithful flatness or finite type of a group image.

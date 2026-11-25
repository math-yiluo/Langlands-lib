# Rigidity over rings with connected spectrum

This internal derived module extends the matrix-weight argument of
`CentralSurjectionImage.BimultRigidity.IsMultG.eq_one_of_isDomain` to coefficient
rings with preconnected prime spectrum. The ring need not be reduced.

`idempotent_eq_zero_or_one` proves that an idempotent in such a ring is zero or
one: its principal open subset is clopen, hence empty or the whole spectrum,
and idempotents are determined by their principal opens.

`IsMultG.eq_one_of_connectedSpectrum` concerns an affine group scheme `G` over
an arbitrary field `k`, a `k`-algebra `R` with preconnected prime spectrum, and a
multiplicative point `p` over the group algebra `R[Λ]`. If a `k`-algebra map
`R → k` specializes `p` to the identity, then `p` is the identity. No smoothness,
finite type, or reducedness assumption is imposed on `G` or `R`.

For every finite matrix-coefficient subcoalgebra of the coordinate Hopf algebra,
the weight matrices are orthogonal idempotents. The zero-weight matrix
specializes to the identity. Its determinant is an idempotent specializing to
one, so preconnectedness forces it to be one. That matrix is therefore
invertible and idempotent, hence the identity. Orthogonality kills every nonzero
weight matrix. Matrix coefficients span the coordinate algebra, so every
nonzero weight vanishes and the original point is the identity.

This is an internal extension of the cited Library proof, using Mathlib's
clopen-spectrum correspondence; it does not claim an independent literature
statement. It supplies the coefficient rigidity needed for the connected
normalizer argument in the proof of `TorusCentralizerNormalizerStatement`
(module `Absolute.TorusCentralizerNormalizerProof`).

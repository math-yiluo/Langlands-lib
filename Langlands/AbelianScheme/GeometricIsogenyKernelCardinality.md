# Geometric isogeny degree and actual kernel points

This internal comparison identifies the cardinality of the actual geometric
point kernel of an isogeny of an abelian scheme over an algebraically closed
characteristic-zero field with its native scheme-theoretic rank at the identity
point. It neither defines the degree through Tate actions nor assumes any Tate
trace or determinant comparison. The universe is arbitrary.

First a finite reduced algebra over a characteristic-zero field is formally
etale: the Artinian reduced algebra decomposes into a finite product of residue
fields, and these fields are separable in characteristic zero. For a finite
flat group scheme over the field, the published Cartier reducedness theorem
applies to its actual coordinate algebra. The published equivalence between
scheme sections and algebra homomorphisms, the count for finite etale algebras,
and the identification of coordinate dimension with native rank then count the
actual sections by that rank.

`kernelSectionsEquiv` identifies sections of the actual scheme-theoretic kernel
with the kernel of `GroupScheme.pointsHom` at the identity geometric point.
`natCard_kernel_eq_nativeRank` applies the preceding section count to that group
kernel. Finiteness and flatness are preserved in the kernel pullback square.
The native rank base-change theorem transfers its rank to that of the original
isogeny at the identity. The statement allows any point of Spec k; this spectrum
has one point.

Provenance is internal, by composition of the published actual kernel pullback,
Cartier reducedness, finite-etale point count and native-rank comparison. It
proves the isogeny case of the degree-to-point-kernel bridge. The assertion that
a nonisogeny has an infinite point kernel remains a separate obligation.

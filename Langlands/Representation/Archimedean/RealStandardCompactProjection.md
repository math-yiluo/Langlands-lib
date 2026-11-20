# Compact projection into the real standard module

`compactProjection` maps compact polynomial functions to the actual
compact-finite standard module of a real block list of the given rank.
It is a linear left inverse to `compactRestriction`.

Extend the compact polynomial to a continuous compact-finite function
by the signed orthogonal part. The right translation formula for the
extension follows by using the same upper triangular factor in the two
Iwasawa products. This gives compact finiteness from that of the
polynomial on \(O(n)\). Apply the two-point sign average
\((1+\chi_i(-1)L_{s_i})/2\) at every diagonal sign reflection, where
\(L_{s_i}\) sends \(F(x)\) to \(F(s_i x)\).
The reflections commute, so each average preserves the other sign
eigenconditions while imposing its own position character's sign. The high-mode
filters at the disjoint induced blocks preserve this sign covariance
and remove the designated low rotation modes.

The resulting compact function extends to the principal series with
the exponents of the list. Its compact Fourier vanishing is the
membership test for the actual standard module. The sign and Fourier
operators depend only on the compact values when evaluated there.
Those of an original standard vector already satisfy both sets of
conditions, so the projection recovers the original vector by
uniqueness of principal series extension.

This internal construction uses the Library's principal series
extension and rotation-window membership criterion.
`averageTrace_eq_compactProjection_integral` applies the kernel formula
with this explicit left inverse.

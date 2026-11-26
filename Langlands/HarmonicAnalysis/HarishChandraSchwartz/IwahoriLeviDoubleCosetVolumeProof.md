# Proof of the Iwahori double-coset volume formula with the Levi index

`iwahoriLeviDoubleCosetVolume` proves the set equality, the index product,
and the Haar formula of `IwahoriLeviDoubleCosetVolumeStatement`. Write
\(K_T=K\cap T\) for each of the Levi and radical subgroups \(T\).
[Statement](IwahoriLeviDoubleCosetVolumeStatement.md)

Put \(J=mKm^{-1}\), \(L=K_MK_N\), and \(H=(J\cap K_M)K_N\). The
Levi intersection normalizes \(K_N\), so the products for \(L\) and \(H\)
are subgroup suprema and can be taken in either order. Inverting the
Iwahori factorization gives \(K=LK_{\bar N}\). The backward contraction
puts \(K_{\bar N}\) in \(J\), so its factor can move past \(m\) into
the right copy of \(K\). It follows that \(KmK=K_NK_MmK\).

The proof uses the embedding of left-coset sets induced by a subgroup
inclusion. Whenever the smaller subgroup contains a representative of
every coset in the larger subgroup, this embedding is surjective and its
source and target have the same natural-number cardinality. Using
\(K=LK_{\bar N}\), \(L=K_MK_N\), and \(H=K_N(J\cap K_M)\) gives
\[
  [K:K\cap J]=[L:L\cap J],\qquad
  [L:H]=[K_M:K_M\cap H],\qquad
  [H:H\cap J]=[K_N:K_N\cap J].
\]
For a point in \(L\cap J\), the ambient product injectivity identifies
its Levi factor in \(L\) with the conjugate by \(m\) of the Levi factor
of its preimage in \(K\). This puts the factor in \(J\), so
\(L\cap J=H\cap J\). The same injectivity applied to a Levi point of
\(H\) gives \(K_M\cap H=K_M\cap J\). Multiplying the indices through
\(L\cap J\le H\le L\) gives the product. Conjugation preserves \(M\)
and \(N\), so \(K_M\cap J=K_M\cap mK_Mm^{-1}\) and, by forward
contraction, \(K_N\cap J=mK_Nm^{-1}\).

`contractedIntersection_relIndex` uses closedness of \(N\) and forward
contraction to express the radical index as the reciprocal of the Haar
scaling of \(n\mapsto mnm^{-1}\) on \(N\). The conjugate of \(K\) is
open, and compactness of \(K\) gives a finite ambient relative index.
`measure_doubleCoset` multiplies this index by \(\mu(K)\). Substituting
the index product gives the Haar formula with the Levi factor.
[Contracted index](ContractionHaarIndex.md) · [Double-coset measure](DoubleCosetMeasure.md)

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French
edition dated 9 July 2026. The calculation after (VII.1.2.2) is on
printed pp. 222–223 (PDF pp. 228–229). V.5.2 gives the Iwahori
factorization on printed p. 123 (PDF p. 129), and V.5.4 gives the
modulus convention on printed pp. 126–127 (PDF pp. 132–133).
Registered as `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The Levi index accounts for the change in the Levi intersection at a
general chamber point in the printed calculation.
[Source correction](../../../notes/errata/renard-vii12-iwahori-volume.md)

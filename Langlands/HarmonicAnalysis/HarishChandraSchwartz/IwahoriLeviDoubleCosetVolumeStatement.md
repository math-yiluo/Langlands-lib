# Iwahori double-coset volume with the Levi intersection index

Let \(G\) be a locally compact topological group and \(K\) a compact open
subgroup. Let \(M,N,\bar N\) be subgroups, with \(N\) closed and both \(N\)
and \(\bar N\) normalized by \(M\). Write \(K_H=K\cap H\). Assume that the
ordered multiplication \(\bar N\times M\times N\to G\) is injective and
that its restriction \(K_{\bar N}\times K_M\times K_N\to K\) is bijective.
For the point \(m\in M\), assume
\[
  mK_Nm^{-1}\subseteq K_N,\qquad
  m^{-1}K_{\bar N}m\subseteq K_{\bar N}.
\]
These two inclusions are `WeakChamberContraction` on the singleton \(\{m\}\).

The proposition states the set identity \(KmK=K_NK_MmK\) and the
natural-number index product
\[
  [K:K\cap mKm^{-1}]
  = [K_M:K_M\cap mK_Mm^{-1}]\,[K_N:mK_Nm^{-1}].
\]
For any left Haar measure \(\mu\) on the Borel sets of \(G\), it gives
\[
  \mu(KmK)=[K_M:K_M\cap mK_Mm^{-1}]\,c_N(m)^{-1}\,\mu(K).
\]
Here \(c_N(m)\) is the positive Haar scaling factor of the automorphism
\(n\mapsto mnm^{-1}\) of \(N\), implemented by
`HaarModulus.closedRestrictCharacter`. Its reciprocal is \(\delta_P(m)\)
in Renard's normalization for \(P=MN\).

The formula applies to the actual Levi and radical point subgroups when
they satisfy the displayed conditions. If \(m\) normalizes \(K_M\), as it
does when it belongs to the split component of \(M\), the Levi index is
one. The corrected formula allows a general Levi point with the two
radical contractions. The principal congruence example for the
\((2,1)\) parabolic of \(\mathrm{GL}_3\) has a nontrivial Levi index.
[Source correction](../../../notes/errata/renard-vii12-iwahori-volume.md)

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French
edition dated 9 July 2026. VII.1.2, calculation after (VII.1.2.2),
printed pp. 222–223 (PDF pp. 228–229). V.5.2 and V.5.4 give the Iwahori
and modulus conventions, printed pp. 123 and 126–127
(PDF pp. 129 and 132–133). Registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

# Double cosets for semistandard parabolics

`Langlands.GroupScheme.SemistandardParabolicDoubleCosetStatement` uses a fixed
maximal split torus \(A_0\) of a connected reductive group \(\mathbf G\) over a
field \(k\). The two inputs are actual parabolic subgroup functors containing
\(A_0\), with their distinguished Levi factors \(M,L\) containing \(A_0\)
and their geometric unipotent radicals. This data is expressed by
`SemistandardSpectralIndex`.

Write \(P,Q\) for the rational points of those parabolics and
\(W_G=N_{\mathbf G}(A_0)(k)/Z_{\mathbf G}(A_0)(k)\).
`semistandardLeviRelativeWeylSubgroup` gives the actual images \(W_M,W_L\) in
that quotient of the normalizer points lying in the two Levi factors. The
proposition gives a bijection
\[
 W_M\backslash W_G/W_L \;\simeq\; P\backslash \mathbf G(k)/Q
\]
with \(W_M[n]W_L\) mapping to \(PnQ\) for every point \(n\) of the normalizer.
The right hand side is the orbit set of the right \(Q\)-action on
\(P\backslash \mathbf G(k)\).

Renard, *Représentations des groupes réductifs p-adiques*, French edition of
9 July 2026, V.4.5 Lemma (printed p. 119, PDF p. 125), takes semistandard
parabolics with standard Levis over a nonarchimedean local field.
Borel–Tits, *Groupes réductifs* (1965), Corollary 5.20 (printed p. 102,
PDF p. 49), supplies the correspondence for two standard parabolics over
an arbitrary field. A rational normalizer point moves the defining
cocharacter of each semistandard triple to the closed dominant chamber.
This transports both its parabolic and its Levi to the corresponding
standard ones. Left and right translation carry the two double-coset
relations and preserve the comparison induced by normalizer points.
This gives the form with arbitrary semistandard Levis as well as the
specialization in V.4.5.

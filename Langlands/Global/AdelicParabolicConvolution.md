# Convolution and nested constant terms on a parabolic quotient

`Langlands.Global.ParabolicTwistedConvolutionStatement` concerns a
continuous, moderately growing function on \(U_P(\mathbb A)M_P(F)
\backslash G(\mathbb A)\). Write \(T_\lambda\) for multiplication by the
Iwasawa height power for \(P\). For a smooth compactly supported adelic
kernel \(h\), the transported convolution
\(D_\lambda=T_{-\lambda}\delta(h)T_\lambda\) preserves continuity, left
invariance and moderate growth. The height bound uses a matrix
representation of positive size. For every standard \(Q\le P\), taking
the \(Q\)-constant term intertwines the transported convolution formula.
The compact used to define the height has Iwasawa coverage for \(P\).

For left invariance, the height power is unchanged by the adelic
radical and by the principal Levi points. Convolution preserves left
invariance since its translations act on the right. For moderate
growth, the Iwasawa decomposition writes each height increment under a
right translation \(t\) as the height of \(kt\) for some \(k\) in the
compact subgroup. The ratio of height powers is thus bounded uniformly
on the kernel support. Submultiplicativity gives a corresponding bound
for the height of \(xt\) in terms of the height of \(x\). Integrating the
resulting bound against the absolute value of the kernel preserves the
height exponent at each fixed parameter.

For the intertwining identity, the rational points of the \(Q\)-radical
act trivially on the input. The joint integrand descends continuously
to the product of the compact radical quotient and the adelic group.
Its support lies in the product of the radical quotient with the
kernel support, so compact-support Fubini exchanges the integrals.
The identities for nested constant terms in
`AdelicStandardConstantTermTwist` let the outer height multipliers
pass through the constant term at both \(\lambda\) and \(-\lambda\).

This implements the action of a compactly supported convolution
operator on constant terms used in Mœglin–Waldspurger, *Spectral
Decomposition and Eisenstein Series*, I.4.5, printed pp. 60–62
(`moeglin-waldspurger-1995-spectral-decomposition`, collection fingerprint
`1ba99fb90916a687503e88c7191dad43b9c4865b68e6b4221a4f2126f2d2f141`).
The nested height compatibility uses the restriction described in
Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*,
§6.10, p. 208
(`bernstein-lapid-2024-meromorphic-continuation-eisenstein-published`,
SHA-256 `6acbe78adf3a7ddff4be0caa92b169f0e609d1245f674a71fbc6989d6aef9268`).

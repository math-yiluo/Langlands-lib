# Adjoint compatibility of spherical base change

`UnramifiedBaseChangeAdjointStatement` says that any unramified base-change
homomorphism between the actual spherical Hecke algebras of
\(\mathrm{GL}_{r+1}\) over two \(p\)-adic fields commutes with
\(f^*(g)=\overline{f(g^{-1})}\). The Haar measure on each group gives its
spherical subgroup volume one. `sphericalHaar_isInvInvariant` identifies
this measure with the normalized general linear Haar measure and uses
its inversion invariance.

Write \(T_i\) for the standard Hecke elements and \(n=r+1\). The central
uniformizer double coset \(T_n\) acts by translation. The inverse of the
\(i\)-th double coset is the central translate of the \((n-i)\)-th
double coset. Since these indicators are real, multiplication gives
\(T_n T_i^*=T_{n-i}\). The reciprocal spectrum satisfies the corresponding
standard scalar relation. Conjugating a character's value on \(f^*\)
therefore gives the Satake character at the conjugate reciprocal
spectrum. Taking the \(l\)-th power of the parameters commutes with
reciprocal and conjugation. The defining evaluation identity for base
change then gives equality after applying each Satake character on the
lower field. `unramifiedBaseChangeAdjoint` concludes by separation of
elements by these characters.

The statement is a consequence of the Library's characterization of
unramified base change by the power map, the Satake character theorem
and the formulas for the standard Hecke elements and scalars. The
characterization by the power map is the one in Henniart–Lemaire,
*Changement de base et induction automorphe pour GL_n en caractéristique
non nulle*, I.1.3, printed p. 6, and I.3.1, printed pp. 24–25. The retained
edition has literature ID
`provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`
and SHA-256 `7af2940c75a75937c1bf9096eb329931d4245cf592e3572db0ff93ec6e76c5e0`.

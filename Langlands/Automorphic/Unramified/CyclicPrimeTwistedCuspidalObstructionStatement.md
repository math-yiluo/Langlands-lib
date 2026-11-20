# The twisted cuspidal obstruction for a prime cyclic extension

`Langlands.Automorphic.Unramified.CyclicPrimeTwistedCuspidalObstructionStatement`
specializes Clozel–Rajan, *Solvable base change*, arXiv:1806.02513v1,
Theorem 1 and equation (1.1), PDF p. 2, to a prime-degree extension and a
finite-order Hecke character. The character `χ` lives over `E`. Its
restriction to the lower idele-class group is `χ.comp ideleClassInclusion`.
`HasNormKernel E` says precisely that its kernel is the norm image from `E`,
so its restriction generates the character group of the cyclic norm quotient.

The excluded relation compares two actual full cuspidal classes.
`IsoClass.galoisConj σ` is pullback along the inverse automorphism, the
same convention as `σπ` in the source. The other operation is the actual
finite-order determinant twist. The statement places no condition on a
spectral presentation and applies to each positive cuspidal rank `r + 1`.

Clozel–Rajan explain the composite-degree descent issue in §1 and at the
end of §2, PDF p. 7. In the descent tower this obstruction is applied over
the bottom prime extension to a candidate lower cusp whose conjugate is a
norm-trivial twist relative to the top extension. Arithmetic of the two
norm quotients is needed to identify the restricted character as faithful
if the twist is nontrivial. The obstruction uses the character-twisted
endoscopic trace comparison in §§4–7 of the source.

`CyclicPrimeTwistedCuspidalObstructionTCStatement` has the additional
hypothesis that `F` is totally complex. Its infinite places split into
complex places, and the finite-order character is trivial on their
connected local multiplicative groups. The comparison at finite places
still uses the actual character twist.

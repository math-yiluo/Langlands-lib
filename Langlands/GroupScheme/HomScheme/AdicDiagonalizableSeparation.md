# Adic detection for diagonalizable group homomorphisms

Let \(A\) be a commutative ring that is separated for the powers of an
ideal \(I\), let \(M\) be an abelian group, and let \(G\) be a separated
group scheme over \(\operatorname{Spec} A\).
`diagonalizableAdicInjectivity` proves that two homomorphisms
from the diagonalizable group \(D_A(M)\) to \(G\) are equal if they agree
after base change to each \(\operatorname{Spec}(A/I^{n+1})\).
The result also applies to sources isomorphic to \(D_A(M)\).

The proof takes the closed equalizer in the slice of schemes over the
base. Agreement on the thickenings makes each diagonalizable quotient
scheme factor through the equalizer. Any element in the kernel of
restriction to the equalizer therefore has all its coefficients in
every \(I^{n+1}\). Adic separation makes these coefficients zero.
The closed immersion has injective pullback on global sections of
its affine target, so it is an isomorphism.

This is an internal comparison for the completed valuation tests in
torus Hom effectivity. It combines the Library's closed equalizer
criterion, diagonalizable scalar extension and coefficientwise
separation.

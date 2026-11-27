# The discriminant of a Hermitian matrix adjoint

Let \(L/F\) be a quadratic field extension with nontrivial automorphism
\(\iota\), and let \(M/F\) be an extension containing \(L\). Suppose an
\(L\)-algebra with unitary involution has a matrix presentation over \(L\)
in which the involution takes \(X\) to \(H^{-1}\iota(X)^t H\), with
\(H\) an invertible Hermitian matrix of size \(2m\).
`relativeDiscriminantClass_of_hermitian` identifies its relative
discriminant in \(H^2(\operatorname{Gal}(M/F),M^\times)\) with the carry
class for the character of the action on \(L\) and parameter \(d^{-1}\).
Here \(d\) is a unit of \(F\) with image \((-1)^m\det H\) in \(L\).
The three fields and the algebra share a universe.

After extending the matrix presentation to \(M\), take lift \(1\) for
automorphisms fixing \(L\) and lift \(H^{-1}\) for the outer coset.
Hermitian symmetry makes the scalar factors of these lifts equal to
\(1\). The determinant formula then has value \(d^{-1}\) on two outer
arguments and \(1\) otherwise. The carry for the quadratic character
has this same table. Chart independence and lift independence identify
this calculation with the class from any supplied chart over \(M\).

This is the relative factor-set form of Knus, Merkurjev, Rost and Tignol,
*The Book of Involutions* (1998), §10.F, Corollary (10.35), printed
p. 131, with the inverse signed determinant as the quadratic cyclic
parameter.

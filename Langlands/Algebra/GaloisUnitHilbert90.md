# Hilbert 90 for units in finite-dimensional algebras

Let \(L/k\) be a field extension, let \(A\) be an associative unital
\(L\)-algebra, and let \(H\) be a subgroup of \(\operatorname{Aut}_k(L)\).
`Langlands.Algebra.SemilinearUnitHilbert90Statement A H` assumes finite
\(H\), infinite \(k\), and finite-dimensional \(A\) over \(L\). For any
semilinear ring automorphism action \(\alpha\) of \(H\) on \(A\), a unit
cocycle \(c\) has a unit \(b\) satisfying
\(c_\sigma\alpha_\sigma(b)=b\) for every \(\sigma\). The theorems
`semilinearUnitHilbert90` and `exists_unit_coboundary` prove this assertion.

The maps \(v\mapsto c_\sigma\alpha_\sigma(v)\) give a semilinear action on
the underlying vector space. Galois vector descent gives an \(L\)-basis of
fixed vectors. In these coordinates, the determinant of left multiplication
by a vector is a polynomial over \(L\), with value one at the coordinates of
the algebra identity. A polynomial vanishing on every tuple of coordinates
from the image of \(k\) is zero, since that image is infinite. Thus some
linear combination over \(k\) has invertible left multiplication and is a
unit. Its coefficients are fixed by \(H\), so this unit satisfies the
required equation.

This is a derived form of Platonov and Rapinchuk, *Algebraic Groups and
Number Theory* (1994), §2.3.1, Lemma 2.8, p. 80, used in §6.7, p. 356.
The proof uses the Library's semilinear vector descent and a determinant
polynomial to allow an arbitrary finite-dimensional \(L\)-algebra.

# The coordinate algebra of a torus over the algebraic closure

For a torus \(T\) over \(F\), let \(K\) be an algebraic closure of \(F\)
and \(S=T_K\) the scalar extension. The coordinate algebra of \(S\) is
isomorphic to the group algebra \(K[X^*(S)]\). The isomorphism takes the
monomial indexed by \(\chi\) to the function given by \(\chi\) itself.
Thus the characters give a \(K\)-basis of the coordinate algebra. The
affine presentation `Lie.coordinateIso` identifies the underlying scheme
of \(S\) with the spectrum of this algebra.

Lean evaluates the character on the universal point of the affine
presentation to express its regular function. The use of
`characterLattice S` records the geometric lattice over \(K\).

This is the coordinate-algebra assertion in Remark 1 of David Renard,
*Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, § V.2.2, printed p. 105 (PDF p. 111).

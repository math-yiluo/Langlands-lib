# Projective and coefficient actions on completed Deligne points

`nilpDeligneCompletedCoefficientFunctor` evaluates the completed base change of Deligne's
point functor on affine `Nilp` algebras of the original integer ring. A point
has an admissible Deligne class and an actual algebra map from the completed
unramified integers. `nilpDeligneCompletedResidueIso` expresses its coefficient
map in residue coordinates by the natural bijection for nilpotent tests.

`nilpDeligneCompletedResidueDivisionAction` transfers the action through this
isomorphism. On the Deligne class it is the projective action of the first
factor. On the coefficient map it is precomposition with the negative power
of actual arithmetic Frobenius, with exponent given by the sum of determinant
and reduced-norm orders. The proof reduces the signed powers of completed
Frobenius and applies the residue-coordinate action formula.

The two actions and exponent are those in Drinfeld, *Coverings of p-adic
symmetric regions* (1976), §2A, printed p. 109 (PDF p. 3). In the algebra-map
coordinates, precomposition by the inverse expresses the left action.

The coefficient coordinate uses the scalar tower on the adic completion. [Deligne points over the completed maximal unramified base](DeligneCompletedBase.md) constructs the direct action at the reduced degree with its specified base algebra map.

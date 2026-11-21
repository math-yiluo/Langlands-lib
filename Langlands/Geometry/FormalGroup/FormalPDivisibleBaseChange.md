# Coefficient extension of the actual tower of a formal module

`IsPiDivisible.pDivisibleBaseChangeIso` identifies the actual
`p`-divisible tower of the coefficient-extended formal law with the
pullback of its original tower. The comparison on each finite level
uses the represented scalar kernel and the actual scheme pullback.
The inclusion and transfer morphisms agree under these comparisons.

The tower isomorphism is natural for every integral formal homomorphism.
For an order action, applying naturality to each formal order endomorphism
proves that it intertwines the new order action with the pullback of the
original action. `HeightSquaredModule.pDivisibleBaseChangeIso` specializes
this to the primal tower of a square-height special formal division
module when `p = b * π^e` with `b` a unit and `e > 0`. An integral formal
isomorphism also induces an actual tower isomorphism by restricting its
two inverse maps to the finite kernels.

Harris (1997), Appendix, printed pp. 112–113 (PDF pp. 38–39), uses the
formal order action on a `p`-divisible group and the pullback to the
special fibre in C1. Rapoport–Zink (1996), §6.43, printed p. 309
(PDF p. 321), identifies the primal summand as a special formal module.
The Lean comparison follows from the actual affine presentations of
its finite kernels.

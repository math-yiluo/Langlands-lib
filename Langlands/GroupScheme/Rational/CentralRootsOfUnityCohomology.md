# Finite-order two-cocycles and the relative Hasse principle

`RootsOfUnityPrimitiveAfterRefinement n c` records that the inflation of a
unit-valued two-cocycle `c` for `L/F` to some finite Galois extension `E/F`
containing `L` is the coboundary of a cochain with values of order dividing
`n`. It uses the multiplicative inhomogeneous differential and the actual
restriction homomorphism from `Gal(E/F)` to `Gal(L/F)`.

Suppose `F` has characteristic zero, `n` is positive, and the values of `c`
are `n`-th roots of unity. If `c` has a primitive with values in `Lˣ`, the
`n`-th powers of that primitive form a one-cocycle. Hilbert 90 writes it as
the coboundary of a unit `z`. A splitting field and finite Galois refinement
supply an `n`-th root `y` of `z`. Dividing the inflated primitive by the
one-coboundary of `y` keeps its two-coboundary and makes each value an
`n`-th root of unity.

For number fields, `relativeUnitsClass₂` is the class of the actual
unit-valued cocycle in relative degree-two cohomology. The main local
implication assumes that its finite localization maps and the
archimedean invariants vanish at every indicated place. The Library's
relative Hasse theorem, idele class Hilbert 90 and local invariant family
then give zero for this class. The inhomogeneous cochain comparison gives
a unit primitive, to which the refinement argument applies.

The arithmetic motivation is the roots-of-unity case of Lemma 6.19 in
Platonov and Rapinchuk, *Algebraic Groups and Number Theory* (1994), §6.5,
p. 336 (PDF346). The lemma uses the Brauer Hasse principle for the
roots-of-unity centre. The implemented comparison works on finite relative
cocycles, with vanishing specified on their unit class. The proof is a
finite-Galois cochain version of the Kummer argument.

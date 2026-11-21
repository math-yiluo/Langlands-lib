# Heights of actual products and Cartier duals

A finite level is affine. Its global sections recover the chosen
Hopf coordinates via the actual affine comparison. For two levels,
`productSectionsEquiv` identifies the global sections of their
product with the tensor product of their global sections. Stalk
ranks multiply, and the constant heights of the two towers add.

At each level of the Cartier dual tower, the spectrum has the
underlying finite projective dual coordinate module. The two finite
projective modules have equal rank at every base prime, so Cartier
duality preserves height. Consequently, `HasHeight.splitWithDual`
gives height \(2h\) for the actual polarized product of a tower of
height \(h\) and its dual.

Tate (1967), §2.3, printed p. 166 (PDF p. 5), describes the dual tower
and its equal height. Rapoport–Zink (1996), §6.43, printed p. 309
(PDF p. 321), identifies the actual polarized split product. The
height formula here is derived from the ranks of the two coordinate
algebras on each finite level.

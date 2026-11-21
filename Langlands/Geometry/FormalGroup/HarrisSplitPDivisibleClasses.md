# Isomorphism classes of split polarized affine points

`PolarizedFramedTower.Iso` is an integral tower isomorphism between the
targets. It intertwines all order endomorphisms, preserves the alternating
polarization on every finite level and test scheme, and pulls back to an
isomorphism that intertwines the full rational rigidifiers on the special
fibre. The identity, inverse and composite satisfy these same equations.

`SplitPDivisibleAffinePoint.framedTower` uses the actual split target,
tautological polarization, split order action and full special-fibre
rigidifier of each point. The quotient `IsomorphismClass` identifies
points whenever these actual data are isomorphic. The equation on the
rigidifier concerns the full morphism, so the relation is stated on the
polarized triple recovered from the point.

The isomorphism classes implement the strict polarized form of Harris
(1997), Appendix, printed p. 113 (PDF p. 39), conditions (i)–(iii) of C1,
in the split affine presentation. Rapoport–Zink (1996), §6.43, printed
p. 309 (PDF p. 321), gives the split polarized form of the target. Its
Definition 3.21(v), printed p. 82 (PDF p. 96), imposes existence of a
polarization in the moduli problem of framed pairs.

# Pullback of the split alternating polarization

For a p-divisible group over a commutative ring `R` and an `R`-algebra
`S`, the construction takes a proof of `FiniteCartierDualExactnessStatement`.
It uses the proof to form both actual Cartier dual towers, also in the
application to pullback to the special fibre.

`pullbackSplitPairing` evaluates the original principal polarization
on any two points of the pulled-back split tower at the same finite
level. A point on a test over the new base gives a point over the old
base by composing the test's structure map. The global unit is taken
on the same underlying test scheme.

`baseChangeSplitIso_pairing` identifies this unit with the alternating
pairing after transporting both points through `baseChangeSplitIso`.
The primal projection is the pullback of the original projection. The
dual projection also uses the finite Cartier comparison. Its evaluation
property gives equality for each of the two mixed pairings. The split
alternating pairing is their quotient, so their equalities give the
result on every finite level and test scheme.

The pairing is the tautological polarization of the split product in
Rapoport–Zink (1996), §6.43, printed p. 309 (PDF p. 321), before (6.17).
Harris (1997), Appendix, printed p. 113 (PDF p. 39), condition (iii) of
C1 uses its pullback to the special fibre. The Lean comparison applies
to coefficient base change of the actual split towers.

# Pullback of the rational split rigidifier

For a primal quasi-isogeny `e` and a common nonzero `ℚ_p` multiplier `c`,
`pullbackSplitRigidifier` pulls the split rigidifier back and then applies
the target split comparison. Its source is the pullback of the original
split tower and its target is the split of the pulled-back primal tower.
`baseChangeSplitRigidifier_hom` shows that its forward rational map agrees
with applying the source split comparison and then forming the split
rigidifier from the pulled-back primal and the same `c`.

The split comparisons factor through the product comparison and then the
Cartier comparison on the dual factor. Product naturality gives the square
for the two rational blocks. The second block uses the dual of `e.inv`,
so its square is Cartier naturality for that arrow, multiplied by `c`.
Both constructions use the actual tower duals formed under
`FiniteCartierDualExactnessStatement`.

This pullback identity is derived from naturality of the product and
Cartier comparisons. The split rigidifier comes from Rapoport–Zink (1996),
§6.43, printed p. 309 (PDF p. 321), before (6.17). Harris (1997), Appendix,
printed p. 113 (PDF p. 39), C1(iii), supplies the common rational multiplier
on the special-fibre quasi-isogeny.

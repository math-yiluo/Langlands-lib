# Target comparison for change of affine test

`targetPrimalComparison` compares the split tower of a coefficient-extended
special target with the split of the pulled-back primal tower. It uses the
actual coefficient comparison on the primal tower and its inverse dual on
the other factor. `targetPrimalComparison_order` shows that it intertwines
the full split order actions. The construction takes the proof of
`FiniteCartierDualExactnessStatement` used to form the two split towers.

An isomorphism of strict split polarized affine points gives an integral
target isomorphism. `baseChangeTargetIso` pulls that isomorphism back
and moves it between the two coefficient-extended target towers using the
comparison on each side. This gives the integral target map for changing
the affine test.

The split target comes from Rapoport–Zink (1996), §6.43, printed p. 309
(PDF p. 321), before (6.17). The construction applies to the strict
polarized isomorphism condition on the affine tests in Harris (1997),
Appendix, printed p. 113 (PDF p. 39), C1.

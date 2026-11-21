# The split polarized point over an affine test

Fix a square-height special formal division module `Φ` over `W/(π)`,
where `π` also denotes the image of the central uniformizer in `W`.
For a nilpotent test algebra `T`, `SplitPDivisibleAffinePoint` consists
of a square-height special formal division module over `T`, an
order-linear quasi-isogeny between the two primal towers over `T/(π)`,
and one unit `c` of `ℚ_p`. The primal towers are built from the actual
finite group schemes for the powers of `p`. The identity `p = b * π^e`
with `b` a unit and `e > 0` relates these towers to the central scalar
kernels.

Given finite Cartier exactness, `targetTower` is the product of the
target primal tower with its Cartier dual. It has the tautological
principal polarization and the action of `O_Dᵐᵒᵖ × O_D` given by
`orderAction`. If the central residue cardinality is `p^f`, then
`targetTower_hasHeight` gives height `2 * (e * f * d²)`, where `d` is the
reduced degree of `D`.

`rigidifier` is an order-linear quasi-isogeny between the pullbacks of
the full split frame and target to `T/(π)`. The two split base-change
comparisons identify it with the block map `(q, c * (q⁻¹)∨)`, where `q`
is the specified primal quasi-isogeny. `splitOrderRigidifierOnBaseChange`
carries out this transport for actual towers over two rings with a
common coefficient extension. The construction gives individual points
in the split affine presentation for a fixed frame.

The input and direction of the rigidifier follow Harris (1997), Appendix,
printed pp. 112–113 (PDF pp. 38–39), conditions (i)–(iii) of C1. The
split product and its tautological polarization are in Rapoport–Zink
(1996), §6.43, printed p. 309 (PDF p. 321), before (6.17). The Lean
construction uses the order of factors `O_Dᵐᵒᵖ × O_D`, with the ordinary
order acting on the primal tower.

# Frame action on the strict split polarized classes

For a fixed affine test, `frameAction` gives the action of the actual
split frame similitudes on `SplitPDivisibleAffinePoint.IsomorphismClass`.
The frame has square height, and the supplied ramification factorization
of `p` forms the primal tower. A proof of
`FiniteCartierDualExactnessStatement` supplies its split Cartier dual
and the dual towers of the targets.

`actFrame_rigidifier` identifies the full new special-fibre rigidifier
with the original rigidifier precomposed by the inverse frame similitude.
It uses the composition equation for transported split rigidifiers.
The primal maps compose in their given order and the common multiplier
is multiplied by the inverse frame multiplier.

The generic action on polarized framed towers preserves strict
isomorphisms. The same target isometry still intertwines the rigidifiers
because both rigidifiers are precomposed with the same inverse frame map.
`actFrameIso` applies that construction to the full split towers. The
identity and multiplication laws on actual points therefore give the
left action laws on the quotient.

This is the frame action on the split affine presentation of C1 in
Harris (1997), Appendix, printed p. 113 (PDF p. 39). Rapoport–Zink
(1996), Definition 3.22, printed p. 82 (PDF p. 96), gives the same
inverse-precomposition convention on framed pairs.

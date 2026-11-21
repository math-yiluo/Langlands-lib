# Integral numerators of rational tower maps

`pPower_nsmul_injective` proves cancellation of multiplication by \(p^k\)
on morphisms of the actual \(p\)-divisible groups. Fix a level \(n\). Lift
its universal affine point into level \(n+k\) along the transfer, after a
faithfully flat extension. The factorization of multiplication by
\(p^k\) through this transfer gives equality after inclusion into the
target's level \(n+k\). Cancel the inclusion on affine points and descend
the equality along the faithfully flat map. The universal point then
gives equality of the original morphisms at level \(n\).

`RationalHom.ofHom_injective` uses this cancellation to prove that
integral Hom embeds in its rational tensor product. Localization gives a
nonzero scalar annihilating the difference of two maps with the same
rational image. Remove its unit factor and cancel the remaining \(p\)-power.

`QuasiIsogeny.integralPresentation` chooses integral numerators for an
invertible tensor and its inverse. `IntegralPresentation.scalarComposites`
proves that the two composites are multiplication by the sum of their
clearing exponents as powers of \(p\). The identities follow first in
rational Hom from the isomorphism and then integrally by injectivity.

The factorization of multiplication at finite levels is in Tate,
*\(p\)-divisible groups* (1967), §2.1, sequence (2), printed p. 161
(PDF p. 2). The denominator convention is from Harris (1997), Appendix,
printed p. 112 (PDF p. 38), in the definition of a quasi-isogeny.

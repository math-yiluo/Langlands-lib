# The actual apartment-action kernel on the zero-component normalizer

This internal derived construction restricts the actual affine normalizer action
to `P.normalizerZeroComponent`, the original `N(F) ∩ G(F)^0`. Under the explicit
cover comparison `P.zeroDatum.CoverImageCentralizerNormKernelStatement`, its kernel
is exactly `P.normalizerZero.subgroupOf P.normalizerZeroComponent`. The field
universe is arbitrary. No apartment axiom or normality premise is used.

First, for the actual maximal split torus in `ValuationBuildingData B`, the
kernel of the reduced linear action `translationAction B.i` is the actual
centralizer. If the quotient action is trivial, each relative root evaluates
equally before and after the action on every full real cocharacter. The
contragredient evaluation formula and the published character-separation lemma
`eval_injective` show that the inverse normalizer point fixes every relative
root as an integral character. The published joint spanning theorem for roots
and restricted rational characters then makes its full character action trivial.
The faithful character-action criterion identifies it as a centralizer point,
and closure under inverses gives the assertion for the original point.
Conversely, a centralizer point acts trivially on all real cocharacters and
hence on the reduced quotient. Taking linear parts therefore shows that any
normalizer point acting trivially on the apartment belongs to the centralizer.

For `n ∈ P.normalizerZeroComponent` with trivial affine action, representability
of the actual centralizer supplies `z` with `j(z) = n`. Its ambient value belongs
to `G(F)^0`, hence to the ambient rational common norm kernel. Since it fixes a
point of the nonempty apartment, the published norm-one centralizer fixer lemma
places `z` in the centralizer's rational common norm kernel. The explicitly
retained cover comparison implies the published full centralizer intersection
comparison, which now puts `z` in `P.centralizerZero`. This gives membership of
`n` in the original `P.normalizerZero`. In the reverse direction, every
centralizer-zero point belongs to the centralizer norm kernel, so bundled omega
compatibility makes its action trivial.

`zeroComponentApartmentAction` is the restriction of
`P.apartment.normalizerAffineEquiv` through the subgroup inclusion. Its value
theorem is definitional. The pointwise equivalence above is exactly the kernel
equality for this homomorphism.

The provenance is deduction from published actual-data definitions, character
separation, joint spanning, the norm-one fixer lemma, and the conditional
centralizer-intersection assembly. No new literature assertion is introduced.
The cover comparison, full-normalizer normality, range comparison with the
geometric affine Weyl group, and the closing affine Iwahori–Tits theorem remain
separate obligations.

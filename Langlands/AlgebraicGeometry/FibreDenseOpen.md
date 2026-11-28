# Fibrewise dense opens of smooth schemes

A flat map lifts generizations. An arbitrary base change induces a flat extension on each residue
fibre, so fibrewise density survives base change as well. Finite intersections use stability of
open membership under generization, and images under open immersions use continuity. These facts
implement the fibrewise density properties in Bosch, Lütkebohmert and Raynaud, *Néron Models*
(1990), §2.5, printed p. 55 (PDF p. 62).

For schematic density, compare BLR §2.5 Lemma 1(b), printed p. 56 (PDF p. 63). A section vanishing
on the dense open has zero germ at a same-fibre generization of each point. In an affine chart
this yields a denominator killing the section and invertible at the generization. Its germ at the
original point has nonzero image in the fibre stalk, which is a domain by smoothness.
`quotientStalkEquivFiberStalk` identifies this fibre stalk with the quotient by the extended
maximal ideal of the base stalk. `Langlands.Algebra.localFiberInjectivity` lifts the injectivity
of multiplication by the denominator from the fibre to the stalk, so the section has zero germ
at every point. This proves schematic dominance for open immersions with fibrewise dense image
into a smooth scheme over any base.

The BLR source ID is `bosch-lutkebohmert-raynaud-1990-neron-models` and the file SHA-256 is
`16d0701b4192ae9db91d083c1df69c0492b00a994aee7bcb0abca365d859d529`. The algebraic injectivity
input is Stacks Project, Lemma 10.128.4 in `046Y.html` of the registered snapshot
`stacks-algebra-flatness-criteria-2026-10-22` (snapshot SHA-256
`4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`).

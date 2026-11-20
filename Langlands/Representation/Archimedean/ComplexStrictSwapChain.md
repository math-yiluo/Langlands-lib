# Integrability on a chain of strict complex adjacent-swap charts

`StrictSwapChain` records the list of inducing characters before and after
each adjacent swap. Each step requires the earlier character to have strictly
larger real exponent. The chain chart is the product of the successive rank-one
chart matrices, with the first swap on the left. The coordinate space is a
finite product of complex planes with product Lebesgue measure.

`integrable_modulusSpherical` uses the positive spherical majorant of the
initial standard module. Integrating its value over the first coordinate
gives a positive constant times the majorant for the next list. Induction and
the product integral theorem give a positive constant times the majorant for
the final list. The pointwise norm estimate for smooth standard vectors then
gives absolute integrability on the full product chart.

`intertwiner` composes the individual equivariant operators, with the identity
for the empty chain. `intertwiner_apply` splits the product of complex planes
into the first coordinate and the remaining ones using the
measure-preserving coordinate equivalence. Fubini and the ordinary integral
formula for the first operator then identify the composition with the integral
on the whole product chart. `intertwiner_append` records that splitting a
chain into two consecutive chains factors the corresponding operator.

The majorant proof is an internal step for iterating the rank-one intertwining
integrals of Wallach, *Real Reductive Groups I* (1988), Lemma 5.3.1 and §5.3.4,
printed pp. 144–145 and 147 (PDF pp. 164–165 and 167 of
`wallach-1988-real-reductive-groups-i`). A chain through an intermediate order
is used for the comparison of constituents in Getz and Hahn, *An Introduction
to Automorphic Representations* (2024), Theorem 10.6.4, printed p. 286
(PDF p. 298 of `getz-hahn-2024-automorphic-representations`).

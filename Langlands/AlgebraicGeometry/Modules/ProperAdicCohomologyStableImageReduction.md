# The exact-sequence reduction for stable ideal-adic images

This derived helper implements the diagram chase in Stacks Project Lemma
30.20.4(3), tag 02OB, for the actual module sheaves and canonical quotient
maps of `IdealAdicQuotients`. The registered original source is
`stacks-formal-functions-stable-images-2026-11-04`, `02OB.txt`, proof of
conclusion (3), including comment #11745 correcting the cited kernel bound
to Lemma 30.20.3(3). This helper assumes that kernel bound and does not
prove its geometric uniformity.

`quotientShortComplex` is the sequence `I M → M → M/I M`. Its first map is
the canonical monomorphism and its second map is its categorical cokernel
projection, so `quotientShortComplex_shortExact` proves it short exact.
For an ideal inclusion `I ≤ J`, `quotientShortComplexMap` uses the canonical
map `I M → J M`, the identity on `M`, and the canonical map `M/I M → M/J M`.
The commutative squares follow from the published compatibility equations.

`quotient_cohomology_range_eq_of_ker_le` assumes that the kernel of
`H^(p+1)(I M) → H^(p+1)(M)` is contained in the kernel of
`H^(p+1)(I M) → H^(p+1)(J M)`. It proves that the image of
`H^p(M/I M) → H^p(M/J M)` equals the image of `H^p(M) → H^p(M/J M)`.
The connecting map sends a class in the source quotient to the first
kernel. The assumed containment and naturality show that its image in the
target quotient has zero connecting class. Exactness then lifts it from
`H^p(M)`. Conversely, every class from `H^p(M)` factors through `H^p(M/I M)`
by functoriality of the canonical quotient maps.

The proof uses the published actual right-derived long exact sequence and
its naturality, then translates exactness in `ModuleCat R` into an
existence of preimages. No properness, coherence or noetherian hypotheses
are needed for this conditional diagram chase. The base ring, scheme and
modules lie in an arbitrary universe `u`.

`adic_cohomology_stable_image_of_ker_le` specializes this result to powers
of a fixed ideal. It takes one bound `c` for the degree `p+1` kernel
containment, uniformly for `n + c ≤ k`, and gives the exact corresponding
range equality for `adicTransition` and `adicProjection`, with the same
bound and no change of the canonical maps.

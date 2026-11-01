# Additivity of actual cohomological Euler characteristics

`DerivedSections.EulerCharacteristicAdditivityStatement` asserts
`χ(S.X₂) = χ(S.X₁) + χ(S.X₃)` for an actual short exact sequence `S` of
structure-sheaf modules on a scheme `X` over a field `K`. The scalar action and
cohomology objects are those of the given morphism `f : X ⟶ Spec K`.
Each of the three coefficient sheaves is explicitly required to satisfy
`HasFiniteCohomology f`: every natural-degree cohomology vector space is finite
dimensional, and all sufficiently high cohomology objects are categorically
zero. The Euler characteristic is the published integer alternating sum of
these actual cohomology dimensions.

This is a derived extension of the Stacks Project, Section 33.33, Lemma
33.33.2 (tag [08AA](https://stacks.math.columbia.edu/tag/08AA)), in the registered
snapshot `stacks-euler-characteristics-0BEI-2026-11-01`, lines 176–203.
That lemma assumes a proper scheme and coherent coefficient sheaves, which
ensure the two cohomological finiteness properties. Here those properties are
explicit hypotheses, so no properness or coherence premise is needed. The
derivation uses the published long exact sequence of actual right-derived
sections and finite-dimensional rank-nullity, exactly the numerical ingredients
of the source proof.

The statement allows arbitrary characteristic, empty or disconnected schemes,
and arbitrary module sheaves satisfying the stated finiteness conditions. It
does not assert finiteness for general coherent sheaves, define an intersection
number, or calculate the polarized finite-flat rank.

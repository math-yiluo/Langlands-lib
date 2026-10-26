# Rational spectral actions from norm-continuous base orbits

Author: Worker 36.

This derived construction starts with an actual presented strict affinoid
algebra `P` over a complete ultrametric normed field `K`. Let `G` be a
topological group in an independent universe, and let `ρ : G →* Aut P` be
an algebraic action by bounded `K`-algebra automorphisms. Assume that every
forward orbit `g ↦ (ρ g).hom(a)` is continuous for the quotient norm of `P`.

`RationalSpectralAction.ofNormContinuous ρ hb` constructs the published
`RationalSpectralAction G P` with underlying homomorphism exactly `ρ`.
Thus the given homomorphism is continuous for the restricted rational
spectral topology, whose neighborhoods are finite intersections of actual
rational-locus stabilizers with spectral displacement conditions on
sections of the corresponding rational quotients.

For one rational datum `d`, the published
`isOpen_rationalLocusStabilizer` makes
`H = (locusStabilizer d).comap ρ` an open subgroup of `G`.
Restriction gives a homomorphism from `H` to the actual locus stabilizer.
Its base orbits are continuous by restriction, so the published
`continuous_section_orbit` makes each orbit of a section `b : d.algebra`
continuous in the actual quotient norm. The norm of its displacement
vanishes at the identity. For every positive radius `r`, that displacement
therefore has norm less than `r` on a neighborhood in `H`.

Every point `x` of the actual Banach spectrum of `d.algebra` satisfies
`x(delta) ≤ ‖delta‖`. The norm bound supplies the required uniform spectral
bound for all such points. The open subgroup inclusion maps identity
neighborhoods onto ambient identity neighborhoods. Consequently,
`rationalSpectralSubgroup_mem_nhds_of_normContinuous` proves that the
preimage of each single rational test is a neighborhood in `G`.
Finite intersections and the published finite-test criterion prove
`continuous_rationalSpectralTopology_of_normContinuous`, which provides
the continuity field of the constructor. The underlying-homomorphism
simplification is definitional.

The implementation permits trivial valuations, zero and nonreduced
quotients, empty rational loci and empty finite families. It proves a
sufficient condition for this restricted topology. It does not identify
quotient and spectral norms, establish a converse, or identify the full
analytic automorphism topology. The separate problem of section
continuity for arbitrary rational spectral actions has no norm-orbit
hypothesis and remains outside this construction.

## Provenance

The underlying geometry follows Berkovich, *Non-archimedean analytic
spaces* (Trieste lectures, 2009), section 2.1 and Definition 2.1.2, p. 7
(quotient norms and strict affinoid presentations), Definition 2.1.11,
p. 8 (bounded maps), and Definition 2.2.1 and Exercise 2.2.2(ii), p. 9
(rational quotients). Registered source:
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.

Berkovich's unfinished *Etale equivariant sheaves on p-adic analytic
spaces* (1995–1996), section 1.1, pp. 1–2, motivates finite local-function
tests and domain-preserving subgroups for continuous operators.
Registered folder:
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder SHA256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`;
member `Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
SHA256 `91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
The sufficient norm-orbit criterion implemented here is an internal
deduction from the Library's rational stabilizer openness, section-orbit
continuity and restricted spectral topology constructions. Neither
source is asserted to contain this exact criterion as a numbered result.

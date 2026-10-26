# Quotient-norm topology of an invariant rational section action

Author: Worker 36.

This derived construction starts with an actual unit-radius rational quotient
`d.algebra` of a presented strict affinoid algebra `P` over a complete
ultrametric normed field `K`. An algebraic homomorphism
`ρ : G →* locusStabilizer d` acts through the published
`stabilizerSectionAction`. The group and field have independent universes.

`sectionIsometrySubgroup d ρ` consists exactly of the parameters whose actual
section operators preserve every quotient norm. The identity and product laws
follow from the existing section-map laws. For inversion, apply norm
preservation to the inverse operator's image and use
`sectionMap_inv_apply`. `isometry_sectionMap` applies norm preservation to a
difference, proving preservation of distances.

Assume `G` is a topological group and every forward base orbit is continuous
in the norm topology of `P`. The published `continuous_section_orbit` makes
each quotient coordinate orbit continuous. Every coordinate has norm at most
one, and the identity operator fixes it.
`eventually_section_contractive` therefore applies the published finite
coordinate estimate `eventually_contractive_of_coordinates`: on one
neighborhood of the identity, all section norms decrease under every operator.
No common operator bound is an input.

Continuity of inversion pulls that neighborhood back to a neighborhood on
which the inverse operators are also contractive. Applying the inverse bound
to a forward image gives the reverse inequality, hence equality.
`eventually_section_isometry` puts a neighborhood inside the full norm
isometry subgroup. Mathlib's `Subgroup.isOpen_of_mem_nhds` then constructs
`sectionIsometryOpenSubgroup d ρ hb`, with the same exact membership predicate.

For joint continuity at `(1,b)`, compare the image of a varying section `c`
with the image of the fixed section `b`. Local contractivity bounds this
distance by `dist c b`; continuity of the orbit of `b` bounds the remaining
distance. Two bounds by half of an arbitrary positive tolerance prove
`continuousAt_section_evaluation_one`. At `(g,b)`, translate the group
parameter by `g⁻¹`, use that identity-center result, and compose with the
fixed continuous bounded operator at `g`. The multiplication law identifies
the result with the actual evaluation map. Thus
`continuous_section_evaluation` proves continuity of
`(g,b) ↦ (stabilizerSectionAction d (ρ g)).hom(b)` for the product topology.

The implementation permits trivial valuations, zero and nonreduced
quotients, empty rational loci and empty coordinate types. The isometry
subgroup concerns the constructed presentation's quotient norm; its
openness is a local conclusion and does not assert norm preservation by
every element of `G`. These constructions do not identify the quotient norm
with a spectral norm, identify the full analytic automorphism topology, or
construct general analytic spaces or an equivariant etale site.

## Provenance

The local geometry comes from Berkovich, *Non-archimedean analytic spaces*
(Trieste lectures, 2009), section 2.1 and Definition 2.1.2, p. 7 (actual
quotient norms and strict affinoid presentations), Definition 2.1.11, p. 8
(bounded maps), and Definition 2.2.1 and Exercise 2.2.2(ii), p. 9 (rational
quotients). Registered source: `berkovich-2009-trieste-analytic-spaces`, PDF
SHA256 `8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.

Berkovich's unfinished *Etale equivariant sheaves on p-adic analytic spaces*
(1995–1996), section 1.1, pp. 1–2, motivates control of operators by local
functions on compact analytic domains. Registered folder:
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder SHA256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`;
member `Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
SHA256 `91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
Its spectral small-displacement topology is a separate construction.
The norm-isometry subgroup and joint quotient-norm evaluation proved here
are internal deductions from the Library's actual rational section action
and coordinate-contractivity/orbit-continuity theorems. They are not
numbered claims quoted from either source.

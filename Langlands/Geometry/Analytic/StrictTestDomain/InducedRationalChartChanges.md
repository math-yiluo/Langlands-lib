# Bounded coordinate changes between induced rational charts

This internal construction equips the previously published induced rational
charts with actual bounded algebra coordinate changes. It is a prerequisite
for an affinoid atlas, not a construction of the full analytic category.

The base field `K` is a complete ultrametric normed field. The ambient algebra
`P` is a presented strict affinoid algebra, constructed as a finite Tate algebra
modulo a closed ideal. The topological group `G` acts through a
`RationalSpectralAction`, and `X` stores an open subgroup `H` preserving an actual
rational locus. The local algebra `A = X.domain.obj.algebra` is the constructed
rational quotient algebra. Its spectrum is `X.LocalSpectrum`; the induced space
is the balanced quotient of `G × X.LocalSpectrum`. The independent universes of
the field and group are retained.

## Overlaps

The chart with label `a : G` sends `x` to `[a,x]`. Its open domain is the fiber
over the left coset `aH` of the published component map.
`inducedChartDomain_eq_of_coset_eq` identifies domains with equal coset labels;
`disjoint_inducedChartDomain_of_coset_ne` proves disjointness for unequal labels.
`coset_eq_of_mem_inducedChartDomains` recovers equality of labels from a point
in both domains.

`nonempty_inter_inducedChartDomains_iff` states that two domains have nonempty
intersection exactly when their labels agree and the local spectrum is nonempty.
The forward proof uses the point's component and a chart preimage. The reverse
proof uses a local point and equality of the two domains. No nonemptiness or
finite-index hypothesis is imposed. In particular, equality of empty chart
domains does not imply equality of coset labels.

## Bounded algebra coordinate changes

For equal labels `aH = bH`, `chartChangeElement a b hab` is the element
`h = a⁻¹b` of `H`. Its membership follows from equality in the left-coset
quotient. Its identity, inverse and composition formulas follow by subgroup
extensionality and the group laws:

* `h(a,a) = 1`;
* `h(b,a) = h(a,b)⁻¹`;
* `h(a,c) = h(a,b) h(b,c)`.

`chartSectionAction` restricts the already constructed bounded action on the
fixed rational quotient algebra to `H`. It does not assume a new section action:
the imported construction transports a rational presentation and applies the
proved bounded rational restriction. `chartSectionAction_comp_baseMap` records
its compatibility with the forward ambient algebra operator.

`chartAlgebraChange a b hab` is the inverse of this section automorphism at `h`.
It pulls algebra coordinates from chart `a` to chart `b`. `chartBoundedChange`
packages its forward and inverse maps as an actual bounded algebra equivalence.
If `q : P → A` is the rational base map, the pullback satisfies

`chartAlgebraChange(a,b).hom ∘ q = q ∘ ρ(a⁻¹b).inv`.

`chartAlgebraChange_comp_baseMap` obtains this equality from the forward section
action formula at `h⁻¹`. `chartAlgebraChange_unique` uses the published rational
extension uniqueness theorem: any bounded algebra map with this base
compatibility equals the constructed pullback. It does not infer algebra-map
equality merely from equality on spectral points.

The identity, inverse and cocycle laws are
`chartAlgebraChange_refl`, `chartAlgebraChange_symm` and
`chartAlgebraChange_trans`. The last has the contravariant order

`pullback(a,c) = pullback(b,c) * pullback(a,b)`.

`chartAlgebraChange_hom_trans` expresses the same formula as composition of
actual bounded algebra maps. The proofs apply the subgroup formulas and the
monoid-homomorphism laws of the existing section action, followed by inversion.

## Realization on the actual spectrum

`chartCoordinateChange a b hab` is the spectrum homeomorphism of
`chartBoundedChange a b hab`. It sends a point expressed in chart `b` to its
coordinates in chart `a`. By definition, it is the point action of `h = a⁻¹b`:
the forward point action is comap along the inverse section operator.

`inducedChart_chartCoordinateChange` proves

`chart(a, chartCoordinateChange(a,b,x)) = chart(b,x)`.

It applies the previously proved balanced-quotient identity
`chart(a*h,x) = chart(a,h • x)` and `a*(a⁻¹b) = b`.
`chartCoordinateChange_unique` uses the established chart embedding to prove
uniqueness of this point coordinate. The point identity, inverse and cocycle
laws follow from the same subgroup formulas and the local group-action laws.
All spectra and homeomorphisms here carry their previously constructed
topologies.

## Provenance and scope

Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993),
section 1.2, Definition 1.2.3 and Remark 1.2.4(i), printed p.16 / PDF p.13,
requires actual bounded algebra restrictions in an affinoid atlas and records
their composition law. Registered source `berkovich-1993-etale-cohomology`,
SHA256 `06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
This module constructs coordinate changes for equal coset-chart domains; it
does not claim to implement that general definition.

Berkovich, *Étale equivariant sheaves on p-adic analytic spaces*, unfinished
1995–1996 manuscript, Construction 1.1.2, printed/PDF p.2, supplies the left-coset
copy convention and the subgroup operator used when representatives change.
The registered folder source is
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder SHA256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`.
The member PDF is
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
SHA256 `91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
The inverse on algebra pullback follows from the published contravariant
spectrum action, and the overlap and uniqueness results are internal
deductions. No source-specific errata file was present in the workspace,
current Library or shared notes when these passages were read.

Affinoid-domain universal properties for chart inclusions, a general affinoid
atlas, refinement and gluing, the analytic morphism category, structure-sheaf
descent, analytic sites and the Harris tower specialization remain separate
obligations. The input rational spectral topology is the restricted one already
specified in `RationalSpectralAction`; this module makes no new claim of
continuity for the full analytic automorphism topology.

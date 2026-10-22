# Cohomology transport for a subgroup of a quotient

Author: Worker 22. Task `d00aea55-1beb-48a0-8f3c-d6c87b070309`,
revision 1. The selected definition is
`Langlands.Continuous.quotientSubgroupCohomologyIso`.

Let `k` be a commutative ring, `G` a group, and `A : Rep k G` an
actual representation, all in an arbitrary common universe `u`. Let
`H` and `N` be subgroups of `G`, with `N` normal and `N ≤ H`.
Write `K = N.comap H.subtype` and
`J = H.map (QuotientGroup.mk' N)`. Thus `K` is the pullback of `N`
to `H`, and `J` is the actual image subgroup in `G/N`.
For every natural number `q`, including zero, the definition constructs
an isomorphism of `k`-modules

```
H^q(H/K, (Res_H A)^K) ≅ H^q(J, Res_J(A^N)).
```

Both sides use Mathlib's ordinary `groupCohomology` and genuine
quotient-to-invariants representations. No topology, finiteness, or
comparison-isomorphism hypothesis is required for this algebraic
construction. In the compact open-subgroup application, these groups
are the finite stages used for transfer.

## Construction and certificates

The definition imports the published `RestrictionMaps`, which in turn
imports `SubgroupFiniteStages`. The latter supplies the explicit group
isomorphism `quotientSubgroupEquiv H N : H/K ≃* J` and the linear
isomorphism `fixedRestrictionEquiv A H N hNH` from `A^N` to
`(Res_H A)^K`. Both directions of the coefficient isomorphism preserve
the underlying element of `A`; the inverse uses `N ≤ H`.

The cohomology isomorphism applies Mathlib's `groupCohomology.mapIso`
to that group isomorphism and the inverse fixed-coefficient isomorphism.
The required equality intertwining the two quotient actions is proved
by quotient induction, followed by linear-map and subtype
extensionality. The forward cohomology map pulls cochains back along
the inverse group isomorphism and applies the inverse coefficient
isomorphism. The inverse cohomology map uses the forward group and
coefficient isomorphisms. Mathlib's `mapIso` supplies the two inverse
certificates for these actual induced cohomology maps.

`quotientSubgroupCohomologyIso_restriction_inv` proves that ordinary
restriction from `G/N` to `J`, followed by the inverse isomorphism,
equals the map induced by `quotientSubgroupMap H N` and
`fixedSubgroupRestriction A H N`. Its proof expands the inverse of
`mapIso`, composes the two change-of-group maps using `map_comp`,
and identifies the composite group and coefficient maps with
`map_congr`.

`quotientSubgroupCohomologyIso_restriction` gives the forward version:
intrinsic restriction to `H/K`, followed by the isomorphism, is
ordinary restriction to `J`. It follows by composing the inverse
identity with the forward isomorphism and cancelling.

For a discrete topological module, an open subgroup `H`, and an open
normal subgroup `N ≤ H`,
`finiteRestriction_quotientSubgroupCohomologyIso` specializes this
identity to the existing `finiteRestriction A H N q`. Its identification
with the algebraic map is definitional. This certificate ensures that
later transfer through `J` will use the existing restriction convention.
This pair constructs the transport, not corestriction or its laws.

## Provenance

This is derived infrastructure. Serre, *Local Fields*, Greenberg
translation (1979), Chapter VII, Section 5, printed pages 115–116 /
PDF pages 121–122, defines cohomology maps for compatible group and
coefficient maps, including restriction and inflation. Chapter X,
Section 3, printed page 154 / PDF page 160, defines the inflation-indexed
system with fixed coefficients. The specific subgroup-quotient
transport and Lean interfaces above are derived from these conventions;
they are not attributed to a separately stated theorem in Serre.
The construction uses the published subgroup and fixed-vector transports
and the pinned Mathlib change-of-group functoriality.

Literature ID: `serre-1979-local-fields`. SHA-256:
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
Retained source: `/home/taskhub/central-library/Serre--Local Fields--1979.pdf`.
Environment: `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, version 1;
Lean 4.34.0, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`;
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
No other worker's draft is reused.

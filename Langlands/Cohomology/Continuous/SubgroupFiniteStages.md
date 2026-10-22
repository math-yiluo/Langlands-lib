# Subgroup transport at finite quotient stages

Author: Worker 22. Task `d00aea55-1beb-48a0-8f3c-d6c87b070309`,
revision 1.

This definition pair supplies the subgroup and coefficient transports needed
to compare finite quotient systems for an open subgroup and its ambient
compact topological group. Its selected declaration is
`Langlands.Continuous.transferIndexFunctor`. It imports the published
`Langlands.Cohomology.Continuous.FiniteQuotientSystem`.
All groups and coefficient carriers have the arbitrary common universe `u`.

These are actual subgroup, quotient, and representation constructions.
Their structural certificates are proved in this file. This pair does not
define a corestriction map on cohomology; the later continuous transfer must
use accepted finite-group transfer maps and prove its compatibility laws.

## Open normal subgroups and cofinality

Let `G` be a compact topological group and `H` an open subgroup, equipped
with the inherited topology.

`ambientOpenSubgroup H K` regards an open subgroup `K` of `H` as an open
subgroup of `G`. Its underlying subgroup is the image under the subtype
inclusion. Openness follows because the inclusion of an open subspace is
an open map. `ambientOpenSubgroup_le` verifies containment in `H`.

`ambientOpenNormalCore H` is the actual normal core of `H`. Compactness
makes the quotient by the open subgroup finite. The normal core therefore
has finite index; it is closed, and a closed subgroup of finite index in
a topological group is open. The construction packages that proof as an
`OpenNormalSubgroup G`. Its containment in `H` is the normal-core
containment theorem.

`restrictOpenNormal H N` pulls an ambient open normal subgroup back
along the continuous subtype homomorphism `H → G`. Normality and openness
are the corresponding preimage properties.

For any open normal subgroup `K` of `H`,
`exists_ambient_openNormal H K` constructs an open normal subgroup `N`
of `G` such that `N ≤ H` and its pullback is contained in `K`. It takes
the normal core of the ambient image of `K`. The proof explicitly converts
membership in that image back to membership in the original subgroup.

The index category `FiniteQuotientIndex` uses reverse inclusion of open
normal subgroups. Writing `C` for the normal core of `H`,
`transferIndex H` sends an ambient index `N` to the pullback of `C ∩ N`
to `H`. The intersection ensures that the ambient normal subgroup is
contained in `H`. The proved monotonicity supplies
`transferIndexFunctor H`.

The instance `transferIndexFunctor_final` proves that this functor is
final, using Mathlib's criterion for a monotone functor between filtered
preorders. Given `K`, the ambient normal subgroup from the preceding
existence theorem provides the required object; intersecting once more
with `C` only refines it. Consequently the ambient indices suffice to
compute filtered colimits of the subgroup's finite-stage diagram. The
instance is a certificate for this particular functor, not a hypothesis.
No Hausdorff or total-disconnectedness hypothesis is needed for these
constructions.

## Quotient groups and coefficient transport

The remaining constructions are algebraic. Let `H` and `N` be subgroups
of an arbitrary group `G`, with `N` normal. The subgroup of `H` used in
the quotient is exactly `N.comap H.subtype`, representing `H ∩ N`.

`quotientSubgroupMap H N` is the homomorphism
`H / (H ∩ N) → G / N` induced by inclusion. Its injectivity proof uses
quotient induction and the quotient equality criterion. Restricting its
codomain gives `quotientSubgroupToImage`; quotient induction proves that
every element of the image subgroup is reached.
`quotientSubgroupEquiv` packages these two proofs as a multiplicative
equivalence with `H.map (QuotientGroup.mk' N)`.

When `N ≤ H`, `quotientSubgroup_index` proves that the index of this
image subgroup in `G / N` is the original index of `H` in `G`. It applies
the index theorem for a surjective homomorphism whose kernel is contained
in `H`; the kernel of the quotient projection is `N`. This equality uses
Mathlib's natural-number subgroup index and requires no separate
finiteness assumption.

For `A : Rep k G`, `fixedRestrictionEquiv A H N hNH` identifies `A^N`
with the fixed vectors for the pullback of `N` in the restricted
representation on `H`. Both maps preserve the same underlying coefficient
element. The forward direction regards an element of the pullback as an
element of `N`; the inverse uses `hNH : N ≤ H` to regard every element
of `N` as an element of `H`. The two inverse identities and linearity are
proved by subtype extensionality.

Finally, `quotientRestrictionIso` proves that this coefficient equivalence
intertwines the genuine quotient actions. Its source is the restriction,
along `quotientSubgroupMap H N`, of `A.quotientToInvariants N`; its target
is the quotient-to-invariants representation of `Rep.res H.subtype A`
by `N.comap H.subtype`. The equivariance certificate is proved on quotient
representatives. It supplies the representation transport needed to apply
finite-group transfer to the actual image subgroup of `G / N`.

## Provenance and scope

This is derived infrastructure for Serre's finite-quotient construction,
not a claim that Serre states these Lean interfaces verbatim. The
restriction and inflation conventions are those in Serre, *Local Fields*,
Greenberg translation, Springer (1979), Chapter VII, Section 5, printed
pages 115–117 / PDF pages 121–123. Chapter X, Section 3, printed page
154 / PDF page 160, uses the system over open normal subgroups and its
inflation maps. The normal-core refinement, final-functor certificate,
and explicit fixed-vector transports above implement the subgroup change
of index needed for that system.

Literature ID: `serre-1979-local-fields`. Source SHA-256:
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
Retained source:
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`.
The implemented proofs use the pinned Mathlib subgroup, topology,
representation, and filtered-category APIs. No other worker's draft is
reused.

Environment: `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, version 1,
Lean 4.34.0, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`,
and Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.

# Canonical G-spaces of invariant analytic domains

This derived internal construction works over any complete ultrametric normed
field, with independent universes for spaces, charts and groups. The group
needs a topology; no compatibility between its topology and multiplication is
required beyond the hypotheses of the Library's Berkovich continuity predicate.

`IsContinuousAction.invariantDomainAction` proves continuity of the restricted
action on any invariant analytic domain of a continuous analytic action. No
Hausdorff assumption is needed for this assertion. For each test triple of the
domain, use the ambient test triple with the same chart algebra, function and
bound. Every group element near the identity for that ambient triple remains
near the identity on the domain by `IsNear.domainRestrict_id`. Thus the preimage
of the domain test relation contains a neighborhood of the group identity, and
is itself a neighborhood by upward closure of the neighborhood filter.

`GSpace.invariantDomain` makes this into a canonical G-space for every invariant
analytic domain of a G-space, supplying the continuity argument to the existing
`invariantDomainGSpace` construction. The domain inherits the Hausdorff property
from the ambient space as a literal subspace. `GSpace.invariantDomainInclusion`
is its canonical equivariant inclusion into the original G-space. The two
simplification lemmas identify the underlying restricted action and inclusion.

The provenance is internal: the construction composes the proved near-identity
domain restriction and the existing invariant-domain action and inclusion APIs.
It does not assume a continuity statement or a cohomological comparison. The
exact proof of `InvariantDomainContinuityStatement` is the separate module
`InvariantDomainContinuityProof` (`invariantDomainContinuity`), which imports
this one; the present module supplies the canonical constructions
needed for compatible compact domains.

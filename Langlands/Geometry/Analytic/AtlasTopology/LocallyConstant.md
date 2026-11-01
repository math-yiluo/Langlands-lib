# Local constancy detected by quasinets

Author: Worker 56.

The coefficient type `A` has an independent universe and has no topology,
algebra, action or nonemptiness assumption. The ambient space can be empty
and need not satisfy any separation or compactness hypothesis.

`IsQuasinet.isLocallyConstant_iff` proves that an actual function `f : X → A`
is locally constant exactly when its restrictions to every member of a
quasinet are locally constant for the actual induced subspace topologies.
The forward implication composes with the continuous subtype inclusion.
For the reverse implication, the inverse image of every coefficient subset
is relatively open on every member. The published quasinet openness
criterion makes that inverse image open in `X`.

`LocallyRefines.isLocallyConstant_iff` gives the relative version for a
family that finitely locally refines a target subset `S`. The restrictions
are precomposition with the literal inclusions `V → S` for the family
members contained in `S`. The published
`isQuasinet_restrictedFamily_iff` supplies a quasinet on the unchanged
subspace `S`. A member of this restricted family is the inverse image of a
contained `V`; its natural map to `V` is continuous. Composing with that
map supplies the local restrictions required by the first criterion.

These are internal consequences of the published quasinet topology and
subspace-refinement results in `QuasinetProperties` and
`DomainIntersections`, together with Mathlib's definition of local
constancy. No descended function is assumed and no coefficient topology
is introduced. The results detect a property of a given function; the
separate domain-sheaf construction constructs functions from compatible
local sections.

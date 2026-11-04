# Faithfulness and finiteness of actual reductive relative Weyl groups

Let `k : Type u` be any field, `G` a connected reductive group scheme over
`Spec k`, and `i : T.toGrp ⟶ G` an actual maximal split torus. This module
proves faithfulness of both the existing rational root-span action
`relativeWeylAction i` and the permutation action `relativeWeylRootPermutation i`.
It constructs `IsConnectedReductive.relativeWeylEquivRootActionRange`, a group
isomorphism from the actual quotient `relativeWeylGroup i = N(k)/Z(k)` to its
actual rational root-action image, and proves that this quotient is finite.
The last three theorems express the same faithfulness and finiteness conclusions
for a split maximal torus in the `IsMaximalTorus` convention.

The implemented proof reuses the published theorem
`relativeRootsRestrictedCharactersSpan`: the rationalized actual roots together
with restrictions of rational characters of `G` span the full rational character
space of `T`. Applying the existing
`IsSplitTorus.relativeWeylAction_injective_of_span` and
`IsSplitTorus.relativeWeylRootPermutation_injective_of_span` gives the two
faithfulness results. `MonoidHom.ofInjective` then identifies the quotient with
the root-span action image. For finiteness, reductive smoothness supplies local
finite type, and `IsSplitTorus.finite_relativeWeylGroup_of_span` applies to the
same spanning theorem. That result uses finite actual root support and the
faithful action; hence this is finiteness of the quotient itself.

The torus inclusion is a monomorphism because it is a closed subgroup, and
affineness is supplied by connected reductivity. A split maximal torus is a
maximal split torus by `IsMaximalTorus.isMaximalSplitTorus`, which gives the
final adapters without an additional geometric premise. The argument includes
the empty root set and imposes no restriction on the characteristic or on the
universe of the field.

This is internal derived content: its mathematical inputs and all its
constructions are the cited published Library declarations and the elementary
group isomorphism associated with an injective homomorphism. It supplies an
unconditional faithfulness adapter useful in the rank-one positive-root task.
The proof of the task's positive-root uniqueness statement and its geometric
dimension bound remain separate obligations.

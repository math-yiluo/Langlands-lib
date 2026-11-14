# Relative identity components under open subgroup inclusions

This is internal infrastructure for finite-index enlargements of integral group
models. It uses the published smooth field identity-component geometry and the
Library's all-test relative identity-component predicate. It adds no geometric
hypotheses to that predicate.

For a group-scheme homomorphism `j : H ⟶ G` over a field whose underlying
map is an open immersion, with `G` smooth, `identitySet_subset_range_of_open`
states that the image of `j` contains the entire identity component of `G`.
The published `identitySet_subset_range_fieldOpenProduct` places that component
in the image of the product of two copies of the open subgroup. Since `j` is
a group homomorphism, that product factors through `j` itself.

`image_identitySet_of_open` identifies the image of the identity component of
`H` with the identity component of `G`. Continuity and preservation of the unit
give one inclusion. For the other, the preimage of the ambient component is
preconnected under the open embedding because the whole component lies in
its image. That preimage contains the identity point, so it lies in the identity
component of `H`.

`comp_open` states the relative result over any base scheme: if the ambient
`G` is smooth, composing an existing representative `i : C ⟶ H` with an open
subgroup inclusion `j : H ⟶ G` gives a representative of the relative identity
component of `G`. The proof applies the field image equality to each residue
fibre, composes image sets, and invokes the published
`IsRelativeIdentityComponent.of_range_residueFiber`. All open immersions and
smoothness assertions in the residue fibres follow by base change.

The provenance is derived from the named published Library results rather than
a transcription of a separate source statement. Its intended use is the final
component clause of KP Proposition A.7.1: once a smooth open enlargement is
constructed, that clause follows from the general open-subgroup theorem.

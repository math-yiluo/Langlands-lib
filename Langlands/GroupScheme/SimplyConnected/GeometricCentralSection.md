# A central section from a geometric reductive lift

`IsSimplyConnected.geometricCentralSection` constructs a homomorphic
section of `q : H ⟶ G` over the original field `k` from the following data:
`G` is simply connected semisimple, `H` is affine over `k`, the full kernel
of `q` is central, and a connected reductive group `D` over an algebraic
closure of `k` has a monic homomorphism into `H` over that closure whose
composite with the base-changed `q` is surjective.
`geometricCentralSection_comp` proves the section identity.

The auxiliary `IsSimplyConnected.exists_section_of_geometric_reductive_lift`
first preserves simple connectedness under extension to the algebraic
closure. `IsCentral.kernel_comp` shows that restricting a map to a monic
subgroup preserves centrality of its full kernel: the restricted kernel
maps to the original kernel, and centrality reflects through the monic
subgroup inclusion.

The connected reductive section construction now produces a section into
`D`. Composing with the supplied monomorphism gives a section into the
base change of `H`. The construction in `CentralSectionDescent` descends
it to `k`, using perfectness of the semisimple target and the affine fpqc
algebraic-closure cover.

## Provenance

This is an internal derived construction combining
`SimplyConnected.CentralReductiveSection`,
`SimplyConnected.CentralSectionDescent`, the published preservation of
simple connectedness under field extension, and the actual factored-kernel
comparison. The existence of the supplied geometric reductive subgroup
is a hypothesis, not a conclusion of this module.

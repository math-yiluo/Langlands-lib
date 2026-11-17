# Sections of central surjections onto simply connected semisimple groups

`IsSimplyConnected.centralReductiveSection` constructs a homomorphism
`s : G ⟶ H` for a surjective homomorphism `q : H ⟶ G`, where `G` is simply
connected semisimple, `H` is connected reductive, and the actual kernel
inclusion `kernelι q` is central on every test scheme.
`IsSimplyConnected.centralReductiveSection_comp` proves `s ≫ q = 𝟙 G`.
All groups are over an arbitrary field in the same universe.

The auxiliary theorem `IsSimplyConnected.exists_section_of_central_reductive`
establishes existence before the definition chooses a section. It chooses an
actual closed representative `d : D ⟶ H` of the scheme-theoretic derived
subgroup using `derivedSubgroupRepresentability`. Semisimple perfectness
identifies the identity of `G` as a derived inclusion. The induced map
`m : D ⟶ G` is a central isogeny by
`IsDerivedSubgroup.isCentralIsogeny_map`, and `D` is semisimple by
`derivedSubgroupSemisimple`. The defining property of `IsSimplyConnected G`
makes `m` an isomorphism. The section is its inverse followed by `d`.

## Provenance

This is an internal derived construction from the published Library results
named above. It is the connected reductive, central-kernel case used in the
proof of `SimplyConnectedMultiplicativeExtensionSplitStatement`; it does
not require a multiplicative-type hypothesis or assert a reduction for
arbitrary affine sources. The proof follows the derived-group argument
described here.

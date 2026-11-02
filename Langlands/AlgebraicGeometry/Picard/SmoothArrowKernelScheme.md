# The actual smooth scheme equivalence relation on Picard arrows

This internal construction realizes Artin's endpoint-kernel relation on
actual scheme representatives, preserving its full presheaf kernel pair.
`atlasArrowKernelPresheaf` is the pullback of the complete endpoint map
with itself, and its two projections retain the respective actual arrows.

Given an actual scheme representation of all arrows,
`exists_smoothArrowKernelScheme` uses the proved relative smoothness of
the second kernel projection to represent its base change along that
scheme. The base-change map to the kernel is an isomorphism because the
arrow representation is an isomorphism. Full faithfulness of Yoneda then
gives both actual scheme projections. Relative smoothness of each kernel
projection proves that each scheme projection is smooth, using the full
represented pullback squares. Transport through the representation
isomorphisms also yields an exact presheaf kernel pair on the arrow scheme.

`representedKernel_sectionwise` proves the monomorphic equivalence-relation
conditions on every complete section type. Pullback uniqueness makes the
pair of projections injective. Existence of a relation section is
equivalent to equality after the endpoint map by the pullback's universal
property; equality gives reflexivity, symmetry and transitivity. This
construction uses all tests and all actual arrows, without taking a
quotient or assuming one exists. The first geometric quotient remains a
separate proof obligation.

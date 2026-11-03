# Identifying a generated group from a dominant product

This is an internal adapter for pointed-image generation. It constructs the
fixed `GeneratedImage f` from an independently supplied closed subgroup
`i : H ⟶ G`, a factor `g : V ⟶ H.X`, and a dominant ordered finite product of
`g`, when the underlying scheme of `H` is reduced. It works over an arbitrary
base scheme and in arbitrary universe. The length may be zero: any positivity
needed for the generation theorem must be supplied separately.

The geometric existence, reducedness, smoothness, and connectedness of `H` are
not asserted here. The adapter isolates envelope minimality from those separate
geometric obligations. It is derived from the published all-test envelope and
ordered-product definitions and Mathlib's ideal-sheaf kernel and closed-immersion
lifting APIs, with no additional literature assertion.

`exists_over_factor_of_schematic_precomp` descends a factorization through a
closed immersion along a schematically dominant morphism. If `p ≫ g = h ≫ i`
and the ideal-sheaf kernel of `p` is zero, the kernel of `i` is contained in the
kernel of `g`. The closed-immersion lift then gives the factor over the original
base.

`range_eq_closedImageEnvelope_of_schematic_power` applies this argument to every
closed subgroup competitor receiving `f`. Homomorphisms preserve the ordered
product, so the schematically dominant product into `H` factors through each
competitor after inclusion into `G`. The descended factor supplies membership
on every test scheme, including nonreduced ones. The reverse containment is the
existing minimality of the fixed closed envelope.

`GeneratedImage.ofSchematicPower` packages this equality and the closed inclusion
into an actual representative. `GeneratedImage.ofDominantPower` obtains schematic
dominance from ordinary dominance and reducedness of `H`. Competing closed
subgroups need not be reduced. The final two theorems identify the canonical
factor and all ordered power maps with the originally supplied ones, using
uniqueness of factorization through the inclusion.

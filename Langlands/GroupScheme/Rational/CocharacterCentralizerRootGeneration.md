# Root generation of cocharacter centralizer points

This internal derived lemma concerns a connected reductive group over any
field and a maximal split torus. A subgroup of rational points containing the
whole-torus centralizer and every relative root group with zero cocharacter
pairing contains the rational points of the cocharacter centralizer.

The proof takes the canonical affine representative of the cocharacter
centralizer. The published theorem `dynamicCentralizerReductive` makes it
connected reductive, and the original maximal split torus factors through it
and stays maximal split. Its roots are ambient roots and have zero pairing,
by `relativeRoots_subset_of_factor` and
`relativeRoot_pairing_eq_zero_of_le_dynamicCentralizer`. Root group membership
passes to the ambient group by `RelativeRoot.comp_mem_subgroup`, and torus
centralizer points pass to the ambient centralizer by commutation.
Finally `relativeRootGeneratedSubgroup_sup_centralizerPoints` shows that these
subgroups generate all its rational points.

This is a consequence of the cited Library results, formulated to support
the centralizer containment in the concrete unramified apartment comparison.

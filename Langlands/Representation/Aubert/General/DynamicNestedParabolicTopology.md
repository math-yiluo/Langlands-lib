# Topological prerequisites for actual nested dynamic parabolics

This is an internal prerequisite for the proof of `DynamicNestedParabolicTransitivityStatement`. It does not assert either normalized transitivity isomorphism. All four lemmas preserve the supplied topologies and have no representation-carrier universe restriction.

`localField_secondCountableTopology` proves second countability of an arbitrary nonarchimedean local field in the given valuative topology. The proof equips the additive topological group with its compatible uniformity and chooses a rank-one realization of the existing valuation. Mathlib's compatible valued norm makes this a proper nontrivially normed field, hence a second-countable space. The resulting proposition concerns the original `TopologicalSpace F`.

`rationalPoint_secondCountableTopology` proves second countability for the canonical rational-point topology of an affine group scheme locally of finite type over a second-countable topological field. The actual affine coordinate algebra is finitely generated. A finite polynomial-algebra presentation embeds its algebra-valued points into a finite power of the field. The published affine-scheme and rational-point homeomorphisms transfer that embedding to the actual rational points. No alternative topology is introduced.

`compactLimit_of_closedEmbedding` pulls back the published Jacquet predicate `IsLimitOfCompactSubgroups` along any closed-embedding group homomorphism between the literal subgroup carriers. The image of a compact set lies in a compact subgroup of the target; the comap of that subgroup is compact because a closed embedding is proper.

`subgroupOfToOriginal` is an abbreviation for the existing
`subgroupOfToAmbient` inclusion homomorphism `N.subgroupOf L →* N`.

`compactLimit_subgroupOf` reuses the published compact-limit restriction result for `N.subgroupOf L →* N` when the ambient subgroup `L` is closed. The map sends the actual nested subtype to its original element of `N`; its range is precisely the inverse image of `L`. Consequently the compact-subgroup containment property passes to the actual inner radical used by the nested functors.

These are derived constructions from the existing local-field, affine-point-topology and compact-subgroup-containment APIs. They provide topology and containment inputs only; they neither assume nor prove a Haar-modulus product or a functor comparison.

The local-field result reuses `GeneralLocalField.secondCountableTopology`;
the subgroup inclusion and compact-limit specialization reuse
`RestrictedLeviTopology`. Their formulas and hypotheses are unchanged.

# Actual Levi transport at the simple intersection indices

This internal derived construction identifies the two actual standard Levis
whose simple indices occur in the minimum-representative geometric term for
`r_J i_I`. The source index is `simpleImage cs w⁻¹ J ∩ I` and the target index
is `simpleImage cs w I ∩ J`. The specified lift is retained; the continuous
group equivalence on rational points is `x ↦ n⁻¹ * x * n`.

The finite-label calculation `simpleImage_inv_inter` and
`mapsIntoSimple_intersections` uses conjugacy of simple reflections and
injectivity of their labels. It is valid for every Coxeter element and does
not assert positivity. For the actual character calculation,
`IsMinimal cs J I w` and `minimalityLengthCriterion_proof` show that `w` has
positive images on `I`. The separately supplied `RootLengthComparison` and
`PositiveSimpleReflectionComparison` then identify the simple-reflection
labels with the actual positive character images. This proves the exact
root-set image `rootSet_simpleImage_intersections`.

`intersectionLeviConjugationEquiv` applies the published
`levi_map_conj_of_character_image`, using the named all-test
`StandardLeviConjugationStatement`, to obtain the actual subgroup image.
`normalizerEquiv` and `weylCharacterAction_point_mk` identify the two
presentations of the same actual lift. The published `conjugationEquiv`
restricts inverse conjugation to the actual subgroups and their inherited
topologies. The evaluation theorem is definitional.

The construction requires a field, the displayed affine and monomorphism
instances, finite actual simple-root labels, a Coxeter system on the actual
normalizer/full-centralizer quotient and the two root-sign comparisons.
It has no Weyl-finiteness, splitness, characteristic-zero, nonempty-root or
representation-theoretic hypothesis. The ambient rational points carry any
specified topological-group structure, including the target's canonical
point topology. The connected reductive group, maximal split torus and
generic cocharacter are those of the named standard-Levi assertion.

This pair does not identify a geometric intersection subgroup with a standard
Levi, compare parabolic or radical subgroups, or prove any geometric expansion
or Jacquet composition. Those remain separate obligations in the full
rational Jacquet compatibility proof. It supplies the actual transport between
the displayed standard Levi indices once those obligations are discharged.

Provenance is the internal simple-conjugation and actual-character calculation
described above, using published adapters. Aubert 1995 equation (1.3) and the
proof of Theorem 1.7(2), including equation (1.9) on printed pp.2181–2183,
motivate the exact intersection indices; the implemented argument does not
claim those representation identities as proved.

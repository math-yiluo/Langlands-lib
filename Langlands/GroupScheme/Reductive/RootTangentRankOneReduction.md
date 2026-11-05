# Full root tangents and generic rank-one centralizers

This internal module transfers the entire intrinsic root tangent through an
actual dynamic-centralizer inclusion, then reduces its dimension bound to
the case where all actual roots are pairwise dependent over the integers.
It retains centralizer reductivity and the rank-one dimension bound as
explicit hypotheses. It does not prove the absolute vector-line statement.

For a represented dynamic centralizer of a cocharacter `ζ`, the published
`RootReducedness.weightSpace_le_range_centralizer` puts every weight space
whose character pairs to zero with `ζ` in the range of the actual differential.
The torus factorization and the published differential weight-membership
comparison then prove `map_weightSpace_torusFactor`: the image of that
centralizer weight space is exactly its ambient weight space.

If a character `α` pairs to zero with `ζ`, every positive integral multiple
also pairs to zero. Commutation of submodule image with suprema gives
`map_positiveWeightSpan_torusFactor`, for the full published
`RelativeRoot.positiveWeightSpan`. Monicity of the representing inclusion
makes its differential injective, so `positiveWeightSpanTorusFactorEquiv`
is a linear equivalence induced by that differential. Its coercion lemma
records the actual map on underlying vectors.

For smooth ambient and centralizer groups, a split torus and a nonzero
character, the published `RelativeRoot.tangentSubmodule_subgroup` identifies
the unchanged intrinsic root tangent with its full positive cyclic weight
span. Applying the same weight-space image equality to every character in
that span proves `map_rootTangent_torusFactor`. The corresponding
`rootTangentTorusFactorEquiv` is again the actual differential, restricted to
the intrinsic root tangents. The proof makes no reducedness or multiplicity
assumption and does not identify a root tangent with only its first weight
space.

`finrank_rootTangent_le_one_of_rankOne` uses the published
`RootReducedness.kernelCocharacter` for the chosen nonzero root and finite
ambient root set. The resulting cocharacter pairs to zero with that root;
every ambient root pairing to zero with it is integrally dependent with the
chosen root. The actual affine dynamic centralizer is closed. The explicit
`DynamicCentralizerReductiveStatement` premise gives connected reductivity
of its actual representative. The original torus factors through it and is
maximal there, and the chosen root is a root of this factor. The published
root-comparison and elementary dependence lemmas show that any two of its
roots are dependent over the integers. The explicit `hrank` premise bounds
the full intrinsic root tangent in this centralizer. The linear equivalence
above transfers exactly that bound to the ambient intrinsic root tangent.

The final theorem works over every algebraically closed field in every
universe, with arbitrary characteristic. The transport lemmas themselves
need only a field and the hypotheses displayed in their Lean types. The
provenance is internal composition of published Library constructions and
submodule linear algebra. The two geometric inputs of the final theorem
remain separate proof obligations; no published target or imported file is
changed.

# Rational conjugacy with an isomorphism of source groups

Worker 1271. This internal interface packages the exact form of subgroup
conjugacy used by the published maximal split-torus statement. For maps
`i : H ⟶ G` and `i' : H' ⟶ G`, `SubgroupConjugate i i'` means that an actual
base point of `G` conjugates `i` to `e.hom ≫ i'` for an actual isomorphism
`e : H ≅ H'`. The definition requires neither map to be a monomorphism.

The relation is reflexive, symmetric and transitive. It is preserved by a
homomorphism of ambient group schemes and is invariant under an ambient
isomorphism. These proofs use the published `HomConjugate` relation and its
precomposition and postcomposition lemmas, so the conjugating points remain
actual scheme sections throughout.

The overgroup assembly lemma starts with a specified conjugacy between two
overgroup maps `P ⟶ G` and `Q ⟶ G`. Once the transported source maps are
conjugate inside `Q`, it composes the two rational conjugacies to obtain the
ambient subgroup conjugacy. This is a categorical assembly lemma; it does
not assert existence of minimal parabolics or prove any reductive-group
conjugacy theorem.

All content is derived internally from the existing group-scheme conjugacy
constructions; no new external mathematical result is assumed.

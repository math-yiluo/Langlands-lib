# Smoothness of the scheme-theoretic derived subgroup

`Langlands.GroupScheme.derivedSubgroupSmoothness` proves exactly
`Langlands.GroupScheme.DerivedSubgroupSmoothnessStatement.{u}`.
For an arbitrary field `k : Type u`, an actual affine locally finite type
group scheme `G` over `Spec k`, and any actual homomorphism `d : D ⟶ G`,
the hypotheses `IsDerivedSubgroup d` and `Smooth G.X.hom` imply
`Smooth D.X.hom`. The universe is arbitrary, and the field may be imperfect
or have positive characteristic. There is no connectedness hypothesis.

The implemented proof applies the published conditional construction
`derivedSubgroupSmoothness_of_reducedImageGeneration` from
`Derived.SmoothnessReduction` to the published theorem
`ImageGeneration.geometricallyReducedAffineImageGeneration` from
`ImageGenerationReducedProof`. This supplies the construction's entire
geometric premise, so the resulting theorem has exactly the target type.

The reduction takes the actual commutator morphism from `G.X ⊗ G.X` to
`G.X`. Its source is affine and smooth by base change and composition,
hence locally of finite type and geometrically reduced. The generation
theorem supplies a smooth closed subgroup representing the closed image
envelope of that morphism, allowing a disconnected source.
`Derived.CommutatorEnvelope` identifies this envelope with the
scheme-theoretic derived subgroup on every test scheme. Uniqueness of
representatives gives an actual isomorphism over `Spec k` to the original
`D`, and the reduction transports smoothness along that isomorphism.
Thus the conclusion concerns every exhibiting inclusion `d`, with the
full functor on nonreduced and nonaffine test schemes retained.

This is a derived assembly of the imported proofs. Its mathematical
conclusion is the smoothness assertion of Milne, *Algebraic Groups* (2017),
Corollary 6.19(b), printed p.129 (one-based PDF p.145), whose proof continues
on printed p.130. The Lean proof uses the general
geometrically reduced-source generation theorem and the commutator-envelope
comparison described above.

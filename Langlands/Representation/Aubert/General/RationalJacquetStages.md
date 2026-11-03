# Rational standard Jacquet restriction in stages

This internal adapter specializes `General.JacquetStages` to the literal rational
standard subgroup families. Its assumptions are the existing
`StandardLeviIntersectionStatement` and `StandardCocharacterStatement`, the
connected reductive group and maximal split torus with generic cocharacter,
the canonical `pointTopology`, local compactness and the nonarchimedean group
property on the point group, closed ambient radicals, and closedness of the
chosen coarse Levi `M_J`. The functor comparison also explicitly receives the
compact-limit property of `U_K.subgroupOf M_J` and the actual positive
Haar-modulus product equality described below. Here `I : Finset J` and
`K = leviIndex J I`. The field universe `u` and carrier parameter `v` are
independent; representation carriers have the target's `max (u + 1) v` universe.
No finite-length assumption is needed for this object-level comparison.

`unipotent_sup_inter_of_subset` proves
`U_J ⊔ (M_J ∩ U_K) = U_K`. The reverse radical inclusion and the explicit product
`U_K = (M_J ∩ U_K) U_J` come from the published rational subgroup geometry.
One inclusion is the universal property of the join, and each element on the
other side is a product of elements of its two factors.
`levi_le_normalizer_inter_unipotent` proves that `M_K` normalizes this second
radical: `M_K ≤ M_J` makes it preserve `M_J`, and the fine semidirect
decomposition makes it preserve `U_K`. These two lemmas require no topology.

`standardInnerJacquetModulus` constructs the actual Haar conjugation modulus of
`U_K.subgroupOf M_J` on `M_K.subgroupOf M_J`, then pulls it back to `M_K` by the
inverse of `subgroupOfContinuousEquiv`. The extra equality `hδ` in
`standardJacquetStagesIso` says precisely that the coarse radical modulus on
`M_J`, restricted to `M_K`, times this inner modulus equals the fine radical
modulus on `M_K`. It is an equality of the actual `HaarModulus` characters,
not an assumed normalized-functor identity. This pair does not prove `hδ`.

`standardJacquetStagesIso` compares the actual `jacquetFunctor` at `J`, followed
by `leviNormalizedJacquetFunctor` for the literal restricted decomposition at
`I`, with the actual `jacquetFunctor` at `K`. It instantiates
`normalizedJacquetStagesIso` with `U = U_J`, `M = M_J`, `W = M_J ∩ U_K`, and
`H = M_K`. The inside-Levi copy of `W` equals the literal
`U_K.subgroupOf M_J`; this identifies its closedness and compact-limit premise
with those supplied here. The radical-join equality identifies the direct
quotient with the fine quotient, and the canonical subgroup equivalence
identifies the final Levi actions. The generic adapter supplies the natural
map `[[v]] ↦ [v]` and its inverse. No abstract quotient or replacement subgroup
family is chosen.

The implemented proof is an internal derivation from the published
`RationalInductionStagesGeometry`, `RationalLeviDecomposition`,
`RationalParabolicDecomposition`, `Parabolic`, and `JacquetStages` declarations.
It uses no classification, character independence, geometric lemma, adjointness,
cuspidal-support theorem or Aubert Proposition 3.2. Actual Haar factorization,
normalized induction in stages, exact-K0 term transitivity and general rational
involutivity remain separate proof obligations.

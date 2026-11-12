# Ordered relative-root products onto the actual Dynamic radical

Author: Worker 51.

`Langlands.GroupScheme.RelativeRoot.dynamicRootOrderedProduct` proves exactly
the published proposition `DynamicRootOrderedProductStatement.{u}` in
[`RootProductStatement`](RootProductStatement.md), at arbitrary universe `u`.
The target pair and all of its imports are unchanged.

## What is proved

Fix any field `k`, a connected reductive group `G` over `k`, an actual maximal
split torus `i : S.toGrp ⟶ G` and an arbitrary cocharacter `ν`. Take any
injective enumeration `a : Fin n → characterLattice S` of the indivisible
actual relative roots that pair positively with `ν`. The theorem supplies a
group scheme `U` with a morphism `jU : U ⟶ G` representing the actual all-test
functor `Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)`. It also supplies
group schemes `H r` with morphisms `j r : H r ⟶ G` representing the full actual
relative-root subgroups `subgroup i (a r)`. All of these representatives are
closed subgroups, smooth, connected, unipotent and split unipotent. Finally, it
supplies a scheme isomorphism `e : (∏ᶜ H).X ≅ U.X` such that `e.hom ≫ jU.hom.hom`
equals the actual `orderedMultiplication j`.

Nothing in the target is weakened. It covers every ordering, zero and
nongeneric cocharacters, and the empty product `n = 0`. When `a r` is
multipliable, its factor is still the full actual root subgroup
`subgroup i (a r)`, as in the target. No separate `2 • a r` factor is added,
because the enumeration contains only indivisible roots.

## Implemented proof

The proof composes three published theorems.

1. [`rootRankOneFactorization`](RootRankOneFactorizationProof.md) proves
   `RootRankOneFactorizationStatement.{u}` with no premises. It applies the
   rank-one parabolic covering reduction to the unconditional
   `RelativeRoot.kernelCentralizerComponentReductive`.
2. [`relativeRootRayDecompositionStatement_of_rootRankOneFactorizationStatement`](RootRayFromFactorPairs.md)
   turns this into `RelativeRootRayDecompositionStatement.{u}`. The rank-one
   factorization gives opposite factor pairs, and hence integral coroots. With
   these coroots, distinct indivisible actual roots have disjoint positive
   integral rays. The finite Lie-weight decomposition gives the injective finite
   enumeration of the indivisible positive roots. The existing positive-ray
   equivalence then shows that every positive root lies on one of these rays.
3. [`dynamicRootOrderedProduct_of_rayDecomposition`](DynamicRootProductRayReduction.md)
   proves
   `RelativeRootRayDecompositionStatement.{u} → DynamicRootOrderedProductStatement.{u}`.
   It first realizes the positive-semigroup subgroup as a smooth, connected,
   closed, split-unipotent group `U` through the published `semigroupRealization`.
   `dynamicSemigroupComparison` identifies `U` with the actual Dynamic radical.
   The supplied rays partition the Lie support of `U` into root-ray blocks.
   Over the algebraic closure the published unipotent ordered-product theorem
   applies, and field-extension detection brings it back down to `k`. The
   block factors are then mapped into `G`, and `cyclicRootFunctorComparison`
   identifies them with the actual relative-root subgroups. The isomorphism is
   the source ordered multiplication of `U`, and composing it with `jU` gives
   exactly the ambient ordered multiplication.

Every supplied theorem has its full universe-general statement and no extra
structural premise. The checked axioms are `propext`, `Classical.choice` and
`Quot.sound`.

## Provenance

This module is an internal composition of the published proofs and reductions
named above. It adds no new mathematical assertion. Their authors and sources
are listed in the linked Markdown files. The mathematical target is described
in the unchanged target Markdown: CGP Theorem 3.3.11 applied to the Dynamic
radical, with the relative-root rays and root groups of KP sections 2.6.2,
2.6.7 and 2.6.8. The Lean proof is the composition described above, not the
printed proof.

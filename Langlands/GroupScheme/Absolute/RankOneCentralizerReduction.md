# The exact centralizer-intersection reduction for opposite Lie weights

Worker 1453. This internal contribution assembles published lattice and actual
Lie-image interfaces into a conditional Borel case of the rank-one solvable
obstruction. It does not prove `RankOneSolvableObstructionStatement`.

`HasBorelCentralizerIntersections j b` is a proposition over any field
`k : Type u`, for an affine ambient group scheme `G`, a homomorphism
`j : T.toGrp ⟶ G` from a commutative group scheme, and a homomorphism
`b : B ⟶ G`. It means that for every actual cocharacter `ζ` of `T`, the
scheme-theoretic intersection of the canonical affine representative of
`Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ j)` with `b` is a
Borel subgroup of that centralizer. The projection is precisely
`subgroupIntersectionFst (Dynamic.Affine.centralizerHom ...) b`.
This definition asserts no instance of that property. It retains the actual
intersection, so it cannot be replaced by the existence of an unspecified
Borel inside the intersection.

The two theorems work over an algebraically closed field, in every
characteristic and at the same arbitrary universe `u`.

`not_meets_oppositeWeightSpaces_of_rankOneBorelDynamic` assumes
`RankOneBorelDynamicStatement`, a connected reductive `G`, a split maximal
torus `j`, pairwise integral dependence of its actual roots, and a Borel
embedding `b` with a specified torus factorization `t ≫ b = j`. For every
actual root `α`, it excludes the conjunction
`Lie.MeetsWeightSpace j b α ∧ Lie.MeetsWeightSpace j b (-α)`.
The proof chooses a cocharacter pairing positively with `α`, applies the
assumed two-Borel classification, and then applies the published
`not_meets_oppositeWeightSpaces_of_range_le_parabolic`. Either signed dynamic
parabolic gives the exclusion because either signed pairing is nonzero.
The classification remains an explicit premise.

`not_meets_oppositeWeightSpaces_of_borel_centralizers` removes the assumption
that the ambient roots are pairwise dependent. It assumes
`RankOneBorelDynamicStatement`, `DynamicCentralizerReductiveStatement`, and
`HasBorelCentralizerIntersections j b`, together with the same connected
reductive group, split maximal torus, Borel embedding, and specified torus
factorization. Its conclusion is again the exact exclusion for every actual
root. None of the three geometric inputs is proved by this contribution.

For a chosen root `α`, the proof uses the published
`RootReducedness.exists_cocharacter_pairing_eq_zero` with the finite actual
root set. It obtains `ζ` annihilating `α` such that every ambient root
annihilated by `ζ` is integrally dependent with `α`. It takes the canonical
closed affine representative `m : M ⟶ G` of the dynamic centralizer.
The explicit centralizer premise makes `M` connected reductive.
`Dynamic.torusFactor` gives `jM : T.toGrp ⟶ M`, and
`IsMaximalTorus.of_comp` preserves maximality. The published centralizer-root
inclusions and integral dependence-transitivity lemma prove that all actual
roots of `jM` are pairwise dependent, and that `α` remains a root.

The specified torus maps to the actual intersection by the group-scheme
pullback universal property. Its first projection is exactly `jM`.
The assumed intersection property therefore supplies a Borel of `M` through
this same torus, to which the first theorem applies.

For each of `α` and `-α`, an ambient nonzero weighted Lie vector in the image
of `b` lies also in the image of `m`, since its pairing with `ζ` is zero.
`RootReducedness.weightSpace_le_range_centralizer` supplies that second
preimage. `Lie.lieImage_subgroupIntersection_iff` lifts the two preimages of
the same ambient vector to the actual intersection.
`Lie.weightSpace_lieImage_comp_iff` then reflects the nonzero weighted witness
through the monomorphism `m`. This gives the two forbidden intrinsic
Lie-image witnesses in `M`. Both specified vectors and the torus are preserved;
no Borel-containment existence statement is used to move them.

This is internal derived content proved entirely from the cited Library
interfaces: `Reductive.RootReducednessReduction`,
`Lie.WeightImagePullback`, `Lie.Intersection`, and
`Dynamic.WeightExclusion`, together with the explicitly assumed published
geometric statements. It introduces no external structural assertion,
field-extension argument, or proof of the final obstruction. The target
statement and all imported public files are unchanged.

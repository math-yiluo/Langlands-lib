# Actual split-component embeddings and full-lattice central directions

Authors: Worker 55 and Worker 33. The two private auxiliary proofs follow the
reduction route in Worker 33's shared draft
`Langlands/GroupScheme/Rational/CharacterRestrictionReduction` for Task 3798
(`6d0882ee-6e45-410c-b5a1-86d4544a4ffb`). The split-torus detection step reuses
that draft's code.

`Langlands.GroupScheme.relativeSplitCentralDirections` proves the exact Library
proposition `RelativeSplitCentralDirectionsStatement.{u}` from
`Langlands.GroupScheme.Rational.RelativeCentralDirectionsStatement`. The
universe `u` is arbitrary, and the theorem has no hypotheses. The statement covers
every field, every actual connected reductive `G` and every actual maximal split
torus `i : T → G`. It keeps every actual relative root, including nonreduced ones,
and it includes rank zero.

## Closing step

The theorem applies the published conditional assembly
`relativeSplitCentralDirections_of_centrality_characterRestriction` from
`Rational/SplitCentralDirectionsConstruction` to two arguments:

- `rootAnnihilatorCentrality`, the published proof of
  `RootAnnihilatorCentralityStatement.{u}` from
  `Rational/RootAnnihilatorCentralityProof`. It says that an integral
  cocharacter of a split torus that pairs to zero with every actual relative root
  is central.
- the private theorem `characterRestriction_aux`, which proves
  `CharacterRestrictionStatement.{u}` as described below.

That assembly yields all the conclusions of the target, as its Markdown explains:

- finiteness and dimension `splitTorusRank T` of `V T` and `Vstar T`;
- the dimension of `relativeCentralDirections i`;
- pointwise fixedness under `relativeWeylRealAction`, using actual centrality of
  the embedded split component;
- for every split component `a`, the actual closed factorization `f : A ⟶ T`
  with `groupHom f ≫ i = a`, injectivity of `cocharacterMapReal f`, its range,
  and both restriction kernels.

The assembly needs `CharacterRestrictionStatement` only to identify
`rationalCharacterRank G` with `splitTorusRank A` for a split component `A`.

## Character restriction (private auxiliary proofs)

`centralSplitTorusCharacter_aux : CentralSplitTorusCharacterStatement.{u}`.
Let `χ` be a nonzero rational character of a connected reductive `G`.

1. Apply the published `reductiveCentralDerivedProduct_of_torusSurjectivity`
   (`Reductive/CentralDerivedProductReduction`) to the published proof
   `reductiveCentralTorusSurjectivity` (`Reductive/CentralTorusSurjectivityProof`).
   This gives a central closed torus `i : Z → G`, affine and locally of finite
   type, and an actual derived subgroup `d : D → G`, with epimorphic
   `subgroupProductMap i d`.
2. `IsDerivedSubgroup.characterRestrict_ne_zero_of_epi_subgroupProductMap`
   (`Rational/ProductDetection`) shows that `characterRestrict i χ ≠ 0`, because
   characters vanish on the derived subgroup.
3. `CocharacterDetection.exists_gm_characterRestrict_ne_zero_of_isTorus` gives a
   cocharacter `φ : 𝔾_m → Z` on which the restricted character is still nonzero.
4. Since `𝔾_m` is split (`isSplitTorus_gm`) and `G` is affine,
   `IsSplitTorus.exists_factor_isSplitSubtorus` factors `φ ≫ i` as `π ≫ j`, with
   `j` a split subtorus. The map `j` is central because `φ ≫ i` is
   (`IsCentral.comp`).
5. If `characterRestrict j χ` were zero, then `characterRestrict_comp` would make
   `characterRestrict (φ ≫ i) χ` zero, a contradiction.

`characterRestriction_aux : CharacterRestrictionStatement.{u}`. Injectivity is
the published `characterRestrict_injective_of_centralSplitTorusCharacter`
(`Rational/CharacterRestrictionInjective`) applied to the previous theorem.
Finite index is the published `IsSplitComponent.finiteIndex_range_characterRestrict`
(`Rational/CharacterRestrictionFiniteIndex`).

The two auxiliary theorems are `private`. The public proofs of
`CentralSplitTorusCharacterStatement` and `CharacterRestrictionStatement` belong to
their owning tasks: Task 3873 (`4f432abe-c26e-45a1-97de-0f87624ccf5b`) and
Task 3798.

## Provenance and scope

This file composes published Library proofs and reductions. It cites no external
source for any new mathematical claim; the source route of the target is recorded
in `RelativeCentralDirectionsStatement.md`. The proof adds no structural, rank,
complement, embedding or realization hypothesis. The only axioms are `propext`,
`Classical.choice` and `Quot.sound`.

# The ordinary flag variety in semisimple rank one

Internal helper module of the Task 7586 proof of
`Langlands.GroupScheme.RankOneCentralCoverStatement`. Notation: `k` is a field, `G` a group
scheme over `Spec k`, `T` a commutative group scheme and `i : T.toGrp ⟶ G`.

## Flag data

`FlagData i` bundles:
- a closed subgroup `b : B ⟶ G` with `IsBorelSubgroup b`;
- a torus factor `t : T.toGrp ⟶ B` with `t ≫ b = i`;
- torus conjugacy in `B` (`MaximalToriAreConjugate B`);
- a proper quotient `G → G/B` with exact coset fibres on every test
  (`IsBorelSubgroup.ProperQuotientData b`);
- a rational normalizer point `n` of `i` whose Weyl class is not the identity.

`nonempty_flagData` constructs such data for a connected reductive `G` over an algebraically
closed field, a split maximal torus `i`, and a root `α` of `i`. The construction is the one
already used in `RankOneLocalAssembly.exists_weylPoint`:
- `exists_proper_isBorelPair_of_relativeRoot` gives an ordinary proper Borel subgroup containing
  the torus;
- `solvableMaximalTorusConjugacy` gives torus conjugacy in it;
- `IsBorelSubgroup.properQuotientData_of_solvableProperFixedPoint` with `solvableProperFixedPoint`
  gives the proper quotient;
- `nonidentityNormalizerOfRootedSolvableQuotient` gives the Weyl point.

The quotient is the ordinary flag variety of a Borel subgroup. No quotient by a dynamic parabolic
`P(ν)` and no properness of such a quotient is used.

## The action and two points

For `F : FlagData i`:
- `X` and `q` are the quotient and the quotient map. `act` is the left translation action
  `Dynamic.flagQuotientSchemeAction`, with `act_lift : g · (h ≫ q) = (g * h) ≫ q`.
- `x₀ = 1 ≫ q` is the base point and `x₁ = n ≫ q` its Weyl translate.
- `orbitMap_eq`: the orbit map of a translate `g ≫ q` is right multiplication by `g` (an
  isomorphism, `rmul`) followed by `q`. Hence it is smooth, flat, locally of finite
  presentation and quasi-compact.
- `isFixed_iff`: a translate `g ≫ q` is fixed by a subgroup `j` exactly when `g⁻¹ j g` lies
  in `B` on every test.
- `isFixed_x₀` and `isFixed_x₁`: the torus fixes `x₀` (since `T ⊆ B`) and `x₁` (since `n`
  normalizes `i`).
- `x₀_ne_x₁`: the two points are distinct. Otherwise `n` would be a rational point of the
  smooth connected solvable group `B` normalizing the closed torus `t`. By
  `IsTorus.mem_centralizerPoints_of_mem_normalizerPoints_of_isSolvable` it would centralize `t`,
  hence `i`, and its Weyl class would be trivial.
- `eq_or_eq_of_isFixed`: in semisimple rank one (pairwise dependent roots), every rational point
  fixed by the torus on all tests is `x₀` or `x₁`. By `exists_relativeWeylCosetMap_eq_of_isFixed`
  such a point is `w ≫ q` for a normalizer point `w`. The rank-one Weyl sign embedding
  `IsConnectedReductive.rankOneRelativeWeylQuotientSignEmbedding_of_isMaximalTorus` injects the
  Weyl quotient into `Bool`, so the class of `w` is trivial or equal to that of `n`. The
  centralizer containment it needs comes from `algClosedMaximalTorusCentralizer`.

## Provenance

Internal, assembled from the named Library results. The fixed-point classification follows the
published `HomogeneousQuotient.rankOneFixedPointSignEmbedding`. It is reproved here in the exact
form needed, with the two explicit fixed points `x₀` and `x₁`.

# Derived generation by rank-one Levi factors from a factor dichotomy

Authors: Worker 180.

This module, `Langlands.GroupScheme.SimplyConnected.RankOneLeviDerivedGenerationReduction`,
contains one proposition definition and four theorems, all at arbitrary
universe `u`:

- the definition `RankOneLeviFactorDichotomyStatement` (a proposition, proved in
  the companion module `SimplyConnected.RankOneLeviFactorDichotomyProof`);
- `IsRankOneLeviFactor.subgroup_neg_le_range`;
- `AutomorphicAction.conjugation_isFixed_iff`;
- `exists_range_le_rankOneLeviFactor`;
- `rankOneLeviDerivedGeneration_of_dichotomy`, which proves the published
  `RankOneLeviDerivedGenerationStatement` from the dichotomy and the two
  published statements `SimpleRootSubgroupGenerationStatement` and
  `IsotropicRootSubgroupGenerationStatement`.

The notation is that of `SimplyConnected.RankOneLeviFactors`: `k` is a field,
all group schemes are over `Spec k`, `i : S.toGrp ⟶ G` is a maximal split
torus, `ν` a generic cocharacter, `j : M ⟶ G` represents
`Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i)`, `a : A ⟶ G` is a
rank-one Levi factor (`IsRankOneLeviFactor`), and `d : D ⟶ M` exhibits the
derived subgroup of `M`.

## The dichotomy statement

`RankOneLeviFactorDichotomyStatement` quantifies over a field `k`, a group
scheme `G` with `[IsAffineHom G.X.hom]` and `IsSimplyConnected G`, a maximal
split torus `i`, a generic cocharacter `ν`, a representative `j : M ⟶ G` of
the centralizer of `ν`, a simple relative root `α ∈ simpleRelativeRoots i ν`,
a rank-one Levi factor `a : A ⟶ G` for `α`, a derived subgroup `d : D ⟶ M`,
and a closed normal almost-simple subgroup `b : B ⟶ D` (`IsAlmostSimple B`,
`IsClosedSubgroup b`, `(SubgroupFunctor.range b).IsNormal`). It asserts
that either

- `SubgroupFunctor.range (b ≫ d ≫ j) ≤ SubgroupFunctor.range a`: the image of
  `B` in `G` lies in the image of `A`, or
- for every test scheme `T` and points `x : T ⟶ B.X`, `y : T ⟶ A.X`, the
  points `x ≫ (b ≫ d ≫ j)` and `y ≫ a` of `G` commute.

It does not assume `G` almost simple or isotropic.

Provenance (derived). With `L_α` the Levi subgroup centralizing the
cocharacters orthogonal to `α`, its derived group `G_α` is simply connected
and is the direct product of `A` and the product `K_α` of its other `k`-simple
factors (Milne, *Algebraic Groups* (2022), Theorem 21.51, printed p.439,
registered as `milne-2022-algebraic-groups`); `K_α` lies in the derived group
`D` of `M`. A `k`-simple factor `B` of `D` therefore lies in `A` or in `K_α`,
and in the second case it commutes with `A`. This is the factor analysis
behind the first step of the proof of Theorem A of Prasad–Raghunathan,
*On the Kneser–Tits problem* (1985), printed p.110 / PDF p.5, registered as
`prasad-raghunathan-1985-kneser-tits`. The statement records the dichotomy
for the Library's actual objects; the companion proof module proves it.

## Theorems

### `IsRankOneLeviFactor.subgroup_neg_le_range`

Hypotheses: `G` affine and smooth, `i` with monomorphic underlying morphism,
`S` split, `RelativeRoot.HasRankOneFactorization i`, `α ∈ relativeRoots i`
and `IsRankOneLeviFactor i α a`. Conclusion:
`RelativeRoot.subgroup i (-α) ≤ SubgroupFunctor.range a`.

Proof. `RelativeRoot.exists_rootPoint_actual` gives a nonidentity rational
point `x` of the root subgroup of `α`; rank-one factorization gives an
opposite pair `p` with `n = p.1 * x * p.2` normalizing `i`. By the published
`IsOppositeFactorPair.weylAction_eq_neg`, `n` acts on characters by
`α ↦ -α`, and by `IsOppositeFactorPair.mem_kernelCentralizer` it centralizes
the scheme-theoretic kernel of `α`. The published
`RelativeRoot.kernelCentralizer_le_dynamicCentralizer_of_pairing_eq_zero`
then puts (the restriction of) `n` in the centralizer of every cocharacter
`ζ` with `latticePairing S α ζ = 0`, so condition 7 of `IsRankOneLeviFactor`
shows that conjugation by `n` preserves the image of `a`. For a point `g` of
the root subgroup of `-α`, `RelativeRoot.normalizer_conj_mem` (applied to
`n⁻¹`, which sends `-α` to `α`) puts `n⁻¹ g n` in the root subgroup of `α`,
hence in the image of `a` (condition 5); conjugating back by `n` gives `g`.

### `AutomorphicAction.conjugation_isFixed_iff`

For a homomorphism `e : H ⟶ G` over any base, a point `g` is fixed by
`AutomorphicAction.conjugation e` exactly when, after every refinement, it
commutes with every point `h ≫ e` of `H`. This is the definition of the
fixed subgroup unfolded with `AutomorphicAction.conjugation_act`.

### `exists_range_le_rankOneLeviFactor`

Hypotheses: the dichotomy statement, `SimpleRootSubgroupGenerationStatement`,
`IsotropicRootSubgroupGenerationStatement`, and the data of
`RankOneLeviDerivedGenerationStatement` (`G` affine, simply connected,
almost simple and not anisotropic, `i`, `ν`, `j`, a family `a α` of rank-one
Levi factors indexed by `simpleRelativeRoots i ν`, `d`) together with a
closed normal almost-simple subgroup `b : B ⟶ D`. Conclusion: some `α` has
`SubgroupFunctor.range (b ≫ d ≫ j) ≤ SubgroupFunctor.range (a α)`.

Proof, by contradiction. If no `α` works, the dichotomy says that `B`
commutes with every `A α`. Let `e = b ≫ d ≫ j`. The fixed subgroup `F` of
`AutomorphicAction.conjugation e`, which is the centralizer of `B` in `G`,
is closed representable by the published `fieldFixedSubgroupRepresentability`
(the source `B` is affine). It contains:

- the image of every `a α`, by the commutation just obtained;
- the image of `i`: since `ν` is generic,
  `IsSplitTorus.dynamicCentralizer_eq_torusCentralizer` identifies the range
  of `j` with `torusCentralizer i`, so points of `B` commute with points of
  `S`;
- the root subgroups of `α` and `-α` for every simple `α`, by condition 5 of
  `IsRankOneLeviFactor` and `IsRankOneLeviFactor.subgroup_neg_le_range`
  (using the published `rootRankOneFactorization`).

`SimpleRootSubgroupGenerationStatement` then gives every relative root
subgroup in `F`, and `IsotropicRootSubgroupGenerationStatement` (for the
closed representative of `F`) gives `F = ⊤`. Hence every point of `B`
commutes with every point of `G`, in particular with every point of `B`;
since `e` is a monomorphism (closed subgroups `b`, `d` and the representative
`j`), `B` is commutative, contradicting `IsAlmostSimple.noncommutative`.

### `rankOneLeviDerivedGeneration_of_dichotomy`

Hypotheses: the three statements above. Conclusion:
`RankOneLeviDerivedGenerationStatement.{u}`.

Proof. As above, `j` represents `torusCentralizer i`, so the published
`splitTorusCentralizerDerivedSimplyConnected` makes `D` simply connected.
Let `K` be the subgroup of `M(k)` generated by the images of the rational
points of the intersections `subgroupIntersection j (a α)`. The published
`simplyConnectedAlmostSimpleRationalGeneration`, applied to `D` and the
preimage of `K` under `rationalPoints.map d`, reduces the claim to the
closed normal almost-simple subgroups `b : B ⟶ D`. For such `b`,
`exists_range_le_rankOneLeviFactor` gives `α` with the image of `B` in the
image of `a α`. For a rational point `y` of `B`, the point
`y ≫ (b ≫ d ≫ j)` is then `w ≫ a α` for a rational point `w` of `A α`, and
the pullback property of `subgroupIntersection_isPullback` produces a
rational point of `subgroupIntersection j (a α)` whose first projection is
`y ≫ (b ≫ d)`. So `d(b(y))` lies in `K`.

All theorems use only the standard axioms.

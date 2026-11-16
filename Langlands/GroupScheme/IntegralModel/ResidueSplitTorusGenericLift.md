# Exact residue split-source lifting and integral units

This is an internal consequence of published Library results about exact
Henselian lifting of split subgroup maps, maximal-torus images, split rank,
and integral points. It keeps the prescribed split source throughout the
residue and generic constructions. The new integral map has exactly the
specified composite on the residue fibre, and the units of its generic
source fix any point fixed by the model's maximal-unramified integral points.

## Main statement

`Langlands.GroupScheme.IntegralModel.ResidueSplitTorusGenericLiftStatement`
is a proposition in arbitrary universe `u`. Its theorem is
`residueSplitTorusGenericLift`. Let `F` be a nonarchimedean local field
with the Library's valuation and topology, `R = 𝒪[F]` its integer ring,
and `k = 𝓀[F]` its residue field. The supplied data and hypotheses are:

1. A connected reductive `F`-group scheme `G` and an integral model
   `M : IntegralModel R F G`, whose integral group is smooth. An
   `IntegralModel` already includes affineness and its specified generic
   identification.
2. A commutative integral group scheme `S` with `IsSplitTorus S.toGrp`,
   and an actual map `a : S_F.toGrp ⟶ G` that is a maximal split torus.
   This map is a comparison over `F`; no integral extension of `a` is assumed.
3. A connected reductive `k`-group scheme `Q` and an actual homomorphism
   `q : M.specialFibre ⟶ Q`. For every maximal torus map
   `i : T.toGrp ⟶ M.specialFibre`, the composite `i ≫ q` must be a
   maximal torus of `Q`.
4. No proper rational parabolic subgroups of `Q`: every map `p : P ⟶ Q`
   satisfying `IsParabolicSubgroup p` is an isomorphism.
5. A prescribed map `s : S_k.toGrp ⟶ Q` that is a maximal split torus.
   Its source is the residue base change of the same integral `S` used
   in the generic comparison `a`.
6. A type `Y : Type u` acted on by the rational points of
   `G_K`, where `K = inertiaFixedField F`, and a point `y : Y`.
   Every element of `M.baseChangeUnramified.integralPoints` fixes `y`.

Here `S_F` and `S_k` denote the actual commutative-group-scheme base
changes along the canonical algebra maps. Under these hypotheses there
exists `j : S.toGrp ⟶ M.group` such that:

1. `j` is a closed subgroup map.
2. The exact residue composite satisfies `j_k ≫ q = s`, as an equality
   of homomorphisms with the prescribed source, rather than an equality
   of subgroup ranges.
3. `j_k` is a maximal split torus of `M.specialFibre`.
4. `M.genericTorusMap S j` is a maximal split torus of `G` over `F`.
5. `IsFixedByUnramifiedTorusUnits F (M.genericTorusMap S j) y`.

The last predicate uses the canonical integer-valued valuation on `K`.
It says that, for every `K`-point of the scalar-extended source whose
value under every `K`-rational character has valuation one, its image
under the scalar-extended generic map fixes `y`. The source here is split,
so this character-valuation kernel is its usual unit subgroup. The
statement imposes no characteristic restriction.

## Integral-unit lemmas

The first three lemmas work over any integral domain `R` with specified
fraction field `K`, any model `M`, and a valuation
`v : Valuation K (WithZero (Multiplicative ℤ))` satisfying
`v c ≤ 1 ↔ c ∈ (algebraMap R K).range` for every `c : K`.

`map_genericSplitTorusHom_mem_integralPoints_of_characterKernel`
takes a closed map from a standard integral split torus to `M.group`.
For a generic source point in the character-valuation kernel, each
coordinate character has valuation one. The published
`exists_units_map_eq_of_valuation_eq_one` lifts each coordinate to an
`R`-unit. The integral-point criterion
`genericSplitTorusValue_mem_integralPoints_iff`, together with
`SplitIntegralPinning.eq_pointsEquiv_symm_torusCharEval`, then places the
image of the actual point in `M.integralPoints`.

`map_genericHom_mem_integralPoints_of_split_characterKernel` chooses a
split presentation of an arbitrary split integral source `H`. It transports
the point and its character-kernel membership through the base-changed
presentation, applies the preceding standard-source lemma to `e.inv ≫ j`,
and checks that the resulting composite is exactly `M.genericHom j`.
It retains closedness of `j` and assumes no generic maximality.

`characterValuationKernel_le_integralPoints_of_isSplitTorus` applies that
lemma to the identity map of a model whose integral group is split.
The generic identification transports character-kernel membership, so
the inclusion holds for the model's specified generic group regardless
of its chosen generic isomorphism.

`map_baseChange_genericHom_mem_integralPoints_of_split_characterKernel`
allows commuting coefficient extensions `R → A → L` and `R → K → L`,
with `A` an integral domain, `L` its specified fraction field, and the
corresponding valuation-ring condition on `A ⊆ L`. It needs a split
integral source and a homomorphism `j`, with no closedness hypothesis
on `j`. Regard the source itself as a model with identity generic
identification. Its character-kernel points are integral by the previous
lemma, including after base change to `A`. The actual integral-model
homomorphism defined by `j`, extended by `Hom.baseChangeCoefficients`,
maps these integral points into `(M.baseChange A L).integralPoints`.
The generic compatibility in that model homomorphism identifies its
generic map with the displayed base change of `M.genericHom j`.

## Exact lift and generic maximality

`isMaximalSplitTorus_genericTorusMap_of_same_source` works over an
arbitrary integral domain and fraction field with connected reductive
generic group. Closedness of `j` and splitness of `S` make its generic
map a split subtorus. The same generic `S` is also the source of the
supplied maximal split map `a`. Choose one split presentation of this
source and use it for both maps. The split-rank assertion in
`maximalSplitTorusConjugacy` identifies the number of factors of the
known maximal split torus with `splitRank G`.
`IsSplitSubtorus.isMaximalSplitTorus_of_card_le` therefore proves
maximality of the new map using the reflexive rank inequality. This
argument compares two maps from the same generic source; it asserts
no equality between generic and residue ranks of an arbitrary model.

`exists_closed_splitSource_lift_of_maximalTorus_images` is the more
general Henselian-ring form of the lift. It assumes a Henselian local
integral domain `R`, its specified fraction field `K`, a field `k`
with surjective `R → k`, and the same data `G`, `M`, `S`, `a`, `Q`,
`q`, and `s` over these rings. Smoothness and affineness of `M.group`
give an affine finite-type residue group, as required by the published
`IsMaximalSplitTorus.exists_maximalTorus_commFactor_of_maximalTorus_images`.
That theorem supplies a residue maximal torus `T`, an inclusion `i`,
and a map `f : S_k ⟶ T`. The map `f ≫ i` has exactly the prescribed
composite `s` under `q` and is a maximal split torus of the residue source.

Apply `exists_closed_splitHom_lift` to this closed residue map from
`S_k`. It yields a closed integral `j` with its residue map literally
equal to `f ≫ i`. Substitution proves both the required equality with
`s` and residue maximality. The preceding same-source lemma proves
generic maximality using `a`.

## Unramified application and published inputs

`isFixedByUnramifiedTorusUnits_genericTorusMap_of_isSplitTorus` specializes
the coefficient-unit lemma to `A = fixedFieldIntegers F` and
`L = inertiaFixedField F`. It uses
`MaximalUnramified.valuation_le_one_iff_mem_range` for the valuation-ring
condition. Every source unit therefore maps into the actual
`M.baseChangeUnramified.integralPoints`; applying the supplied point-fixing
hypothesis proves the exact Library unit-fixation predicate. This lemma
requires neither closedness nor maximality of the integral map.

`exists_closed_splitSource_lift_isFixedByUnramifiedTorusUnits` installs
`henselianLocalRing_integer`, applies the general lift with the canonical
surjective residue map, and appends this unit-fixation conclusion.
The final wrapper proves precisely the displayed main proposition.

The substantive published inputs are:

- `IntegralModel.SplitIntegralPoints` and
  `IntegralModel.UnramifiedGenericSplitTorus` for the coordinate
  integral-point criterion and lifting valuation-one scalars to units;
- `IntegralModel.BaseChangeCoefficientHom` for the actual coefficient
  model morphism and its generic compatibility;
- `Torus.MaximalTorusImageSplitLift` and
  `Torus.HenselianSplitSubgroupLifting` for the prescribed residue map
  and its exact closed integral lift;
- `Rational.SplitRankMaximality` and
  `Rational.MaximalSplitTorusConjugacyProof` for generic maximality;
- `IntegralModel.UnramifiedSplitMaximalTorus` for `genericTorusMap`,
  `Geometry.Building.TorusUnitFixedPoint` for the unit-fixation predicate,
  and `BruhatTits.IntegralModels.DepthZeroInduction` for
  `henselianLocalRing_integer`.

This module constructs no building model or comparison `q`, proves no
maximal-torus preservation or absence of proper parabolics for an actual
building quotient, and supplies neither the comparison `a` nor the residue
map `s`. Those are explicit geometric inputs. Its fixation hypothesis is
on the actual maximal-unramified integral-point group of the supplied
model. Consequently this supporting result alone does not prove
`UnramifiedFixedPointSplitTorusStatement`.

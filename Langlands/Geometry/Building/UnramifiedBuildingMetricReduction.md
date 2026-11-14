# Maximal-unramified building metric: reduction to a retraction distance

This module splits the open target `UnramifiedBuildingMetricStatement.{u}` into
the published common-apartment statement and one new, focused proposition about
the supplied root-valuation building over `K = inertiaFixedField F`. It **proves**
that these two propositions imply the target. It proves neither of them, and it does
**not** prove `UnramifiedBuildingMetricStatement`. The remaining analytic input,
discreteness of normalizer orbits in the apartment, is proved here from published
results. Everything is stated and proved at an arbitrary universe `u`.

## New definition

`KPApartmentData.rootDistance D x y`: for a KP apartment datum `D` with apartment
`D.Apartment` (an affine space over `TranslationSpace i = V(S)/V(S)^Φ`),

    rootDistance x y = sqrt (∑ᶠ α : relativeRoots i, (rootForm i α (x -ᵥ y))²),

the Euclidean distance given by the actual relative roots as coordinates. The sum is
a `finsum`. When the relative roots of `i` form a finite set, which holds for a
maximal split torus of a connected reductive group, it is the ordinary finite sum.
This is the same quantity as the Library's apartment metric
`RootTranslationMetric` (`ValuationApartmentMetric.lean`), which the proof uses.
The quadratic form `∑ α(v)²` is unchanged by every linear automorphism permuting
the roots, in particular by the relative Weyl group. It is therefore a
Weyl-invariant Euclidean metric in the sense of the opening of KP Section 4.2.

## New propositions

The new premise quantifies over a nonarchimedean local field `F : Type u`, an
affine group scheme `H` over `Spec K` (`IsAffineHom H.X.hom`), and a building datum
`B : MaximalUnramified.BuildingData F H`. This is the same quantification as the
published `MaximalUnramified.CommonApartmentsStatement`. `B.ReducedBuilding` is the
supplied quotient of KP (7.6.2) and `B.apartmentMap : B.Apartment → B.ReducedBuilding`
is `x ↦ [(1, x)]`.

**`MaximalUnramified.RetractionDistanceStatement`.** There is a function
`d : B.ReducedBuilding → B.ReducedBuilding → ℝ` such that

1. `d (g • x) (g • y) = d x y` for every `g` in `H(K)` and all points `x, y`;
2. `d (B.apartmentMap a) (B.apartmentMap b) = B.apartment.rootDistance a b` for all
   apartment points `a, b`;
3. for every apartment point `a` there is a map `ρ : B.ReducedBuilding → B.Apartment`
   with `ρ (B.apartmentMap b) = b` for all `b`,
   `rootDistance (ρ x) (ρ y) ≤ d x y` for all `x, y`, and
   `rootDistance a (ρ x) = d (B.apartmentMap a) x` for all `x`.

The statement does not require `d` to be a metric: the reduction derives that.

**`UnramifiedBuildingMetricReductionStatement`** is the implication

    CommonApartmentsStatement.{u} → RetractionDistanceStatement.{u} →
      UnramifiedBuildingMetricStatement.{u}.

`unramifiedBuildingMetricReduction` proves it. The module also proves that the
same two propositions imply the published
`MaximalUnramified.CompleteNPCMetricStatement` (see "Broader corollary" below).

## Source provenance

The source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), with the
authors' corrections and additions of 1 November 2024.
`RetractionDistanceStatement` is a derived statement: it is a consequence of cited
results for the root-valuation building over `K`, not a verbatim source assertion.

- Opening of Section 4.2 (printed p.168; PDF p.199): a Weyl-invariant Euclidean
  metric `d_A` on each apartment. Corrections PDF p.28 add Axiom 4.1.6 to the
  assumptions of Section 4.2.
- Proposition 4.2.1 (printed p.168; PDF p.199), as corrected on PDF pp.28–29
  ("which is `G`-invariant and"; the replacement of Proposition 1.5.13 by 1.5.6(5)
  and 1.5.6(8)): there is a `G(k)`-invariant function `d` on the building whose
  restriction to every apartment is `d_A`. This gives items 1 and 2 of
  `RetractionDistanceStatement` for the standard apartment `A(S)`.
- Lemma 4.2.2 (printed p.169; PDF p.200): for a chamber `C` of `A`, the retraction
  `ρ_{A,C}` is the identity on `A`, does not increase distances (3), and preserves
  the distance from a point of the closure of `C` (2). For an apartment point `a`
  choose `C` with `a` in its closure; this is item 3. The proof of Proposition 4.2.7
  (printed p.170; PDF p.201) uses Lemma 4.2.2 in exactly this way.
- Lemma 4.2.11 (printed pp.171–172; PDF pp.202–203): a small ball about `x` meets
  only facets whose closure contains `x`, and `g x = x` once `g x` is in that ball.
  Its apartment step for normalizer elements is the proved theorem
  `exists_rootDistance_normalizer_smul_lt_imp_eq` below, not a premise.
- Proposition 7.6.3 and Remark 7.6.5 (printed pp.264–266; PDF pp.295–297) construct
  the building over `K` as the quotient (7.6.2) and give it the building structure
  used above. The corrected Chapter 7 assumptions are on corrections PDF p.33.
- Propositions 4.2.3 and 4.2.7 and Theorem 4.2.10 (printed pp.169–172; PDF
  pp.200–203) are the metric, curvature and completeness conclusions. This module
  re-proves them in Lean from `RetractionDistanceStatement` and common apartments;
  it does not assume them.

Common apartments (KP Definition 1.5.5 via Remark 7.6.5) is the already published
`MaximalUnramified.CommonApartmentsStatement`; its proof is a separate open task.

## The proof of the reduction

**Root metric on the apartment** (namespace `IntegerValuationBuildingData`, for any
`B : IntegerValuationBuildingData v G`). The actual relative roots are finite
(`rootDistanceFintype`, from the published `finite_relativeRoots` for the split
torus `S` of the connected reductive group).
`rootMetricSpace` and `rootNormedAddTorsor` are the torsor metric of
`RootTranslationMetric.normedAddCommGroup`. They are local instances only.
`rootDistance_eq_dist` identifies `rootDistance` with this metric via
`RootTranslationMetric.norm_sq`. The apartment is NPC (`root_nonpositivelyCurved`,
from the inner-product case `isNonpositivelyCurved_of_innerProductSpace`) and
proper (`root_properSpace`, by finite dimensionality).
`exists_normalizer_smul_eq_of_smul_apartmentMap_eq` is relation (7.6.2): if
`g • [(1, a)] = [(1, b)]` then `n • a = b` for some `n` in `N(K)`
(`ApartmentQuotient.mk_eq_mk_iff`).

**Discrete normalizer orbits** (the apartment step of KP Lemma 4.2.11).
`exists_rootDistance_normalizer_smul_lt_imp_eq`: for every apartment point `b` there
is `ε > 0` such that every `n` in `N(k)` (`normalizerPoints B.i`) with
`rootDistance (n • b) b < ε` fixes `b`. The proof uses only published results.
The supplied affine roots form a locally finite reflection arrangement
(`isLocallyFiniteReflectionArrangement_of_hasOppositeFactorPairs` with
`IntegerValuationBuildingData.hasOppositeFactorPairs`). Each `n` acts through
`B.apartment.normalizerAffineEquiv n`, which permutes the affine roots
(`KPApartmentData.normalizerAffineEquiv_mem_rootStabilizer`). The generic
`AffineRootSystem.exists_forall_dist_lt_imp_eq` then gives the radius for the root
metric, and `rootDistance_eq_dist` converts it.

**Gluing.** Assume common apartments and `d` with items 1–3 above.
`smul_apartmentMap_dist` shows each translated chart `a ↦ g • B.apartmentMap a`
pulls `d` back to the root metric, so it is injective (`injective_smul_apartmentMap`).
`isRetractionGluedDistance` verifies the published interface
`Metric.KP.IsRetractionGluedDistance d` for the family of translated apartments
`g • range B.apartmentMap`. Common apartments supply a member containing any two
points. Each member is an NPC metric chart
(`Metric.KP.exists_apartmentMetric_of_injective`). The retraction onto
`g • range B.apartmentMap` centred at `g • B.apartmentMap a` is
`x ↦ g • B.apartmentMap (ρ (g⁻¹ • x))`, using item 3 and invariance. The published
gluing results (`IsRetractionGluedDistance.metricSpace` and
`.isNonpositivelyCurved`) then make `d` an NPC metric. This is KP Propositions
4.2.3(1) and 4.2.7. `H(K)` acts isometrically by item 1.

**Completeness.** This section follows the published
`ValuationBuildingCompleteness.lean` for the root-valuation quotient over `K`.
`smul_apartmentMap_eq_of_dist_lt` places `B.apartmentMap b` and
`g • B.apartmentMap b` in a common translated apartment. Relation (7.6.2) then
reduces `g` to a normalizer element moving `b` by less than `ε`, and discreteness of
the normalizer orbits shows `g` fixes the point. Conjugating extends this to every point
(`exists_forall_dist_smul_lt_imp_eq`, the conclusion of KP Lemma 4.2.11 for points).
`completeSpace_of_isometry_apartmentMap` shows that every point is within distance
1 of a translate of the compact image of a closed unit ball of the proper apartment.
It applies the published `Metric.KP.completeSpace_of_discrete_orbits` (KP Theorem
4.2.10). `exists_metric_of_retractionDistance` collects the metric, its equality with
`d`, completeness, NPC and isometry of `H(K)`. Its discreteness input is
`exists_rootDistance_normalizer_smul_lt_imp_eq`; it has no discreteness hypothesis.

**Coefficient isometry.** `KPApartmentData.rootDistance_galoisAction`: for a Galois
stable apartment datum, each coefficient automorphism `σ` acts on the apartment
through an affine map. Its linear part `galoisTranslationAction σ` satisfies
`rootForm (galoisRootAction σ α) ∘ galoisTranslationAction σ = rootForm α`
(`rootForm_galoisTranslationAction`). `galoisRootAction σ` is a permutation of the
relative roots. So the finite sum defining `rootDistance` is reindexed
(`finsum_comp_equiv`), and `σ` preserves `rootDistance`. This is the derived
coefficient invariance described in `UnramifiedBuildingMetricStatement.md`: the
root-sum metric is the invariant choice.

**Assembly.** `SemilinearApartmentData.nonempty_metricRealization_of_retractionDistance`
takes any semilinear apartment datum `A` on `B` whose apartment permutations preserve
`rootDistance`. It builds `A.MetricRealization` from the glued metric. For the
coefficient isometry, any two points are `g • [(1, a)]` and `g • [(1, b)]` by common
apartments. `action_smul` and `action_apartmentMap` move `A.action σ` to
`rationalConjugate σ g • [(1, A.apartment σ a)]`. The distance is then
`rootDistance (A.apartment σ a) (A.apartment σ b) = rootDistance a b`.
`unramifiedBuildingMetricReduction` introduces the target's data. It applies
`RetractionDistanceStatement` and `CommonApartmentsStatement` to
`UnramifiedBuildingDescent.buildingData iT hGK hiT D C h6` (with `hGK` the published
`connectedReductiveFieldExtensionStatement`). It then applies the assembly lemma to
`UnramifiedBuildingDescent.semilinearData`, whose apartment action is
`KPApartmentData.galoisAction`, with `rootDistance_galoisAction`.

**Broader corollary.** `MaximalUnramified.completeNPCMetricStatement_of_retractionDistance`
proves that the same two inputs (`CommonApartmentsStatement` and
`RetractionDistanceStatement`) imply the
published `MaximalUnramified.CompleteNPCMetricStatement`. That statement asks for a
complete NPC metric with isometric `H(K)` action on every supplied
`B : MaximalUnramified.BuildingData F H`, with no descent or coefficient data. The
proof applies `exists_metric_of_retractionDistance` to `B` directly.

No proof of `UnramifiedTwistedChamberStatement`, `UnramifiedTwistedFixedPointStatement`
or any `LocalSimplyConnected*` statement is used.

## Remaining obligations

- `MaximalUnramified.CommonApartmentsStatement` (published; its proof is a separate task).
- `MaximalUnramified.RetractionDistanceStatement`: the KP Chapter 7 building
  structure of the quotient over `K` (Proposition 7.6.3, Remark 7.6.5) and KP
  Proposition 4.2.1 and Lemma 4.2.2 for it.

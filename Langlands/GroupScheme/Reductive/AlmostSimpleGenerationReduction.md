# Almost-simple generation from actual-root and centre premises

For an actual semisimple group scheme `G` over an algebraically closed field
of arbitrary characteristic and universe, this module constructs
`almostSimpleGenerationIsoOfActualRoots : D ≅ G` whenever the actual closed
inclusion `d : D ⟶ G` contains every closed normal almost-simple subgroup.
Its forward map is exactly `d`, as the companion `_hom` theorem proves.
The construction explicitly assumes three structural propositions:
`NormalReductiveCenterStatement`, `SemisimpleRootGenerationStatement`,
and `SemisimpleNormalRootDichotomyStatement`. None is proved here.

`IsGeneratedByNormalAlmostSimpleSubgroups G` records the local generation
property, using the published corrected `IsAlmostSimple` and full subgroup
functors. The implemented helpers are:

- `range_le_identityCore_of_smooth_connected`: a homomorphism from a smooth
  connected group into an affine locally finite-type group factors through
  the target's reduced identity component. Smoothness implies reducedness
  over the algebraically closed field, and the published reduced-subgroup
  lift and identity-component factorization give the factor.
- `IsGeneratedByNormalAlmostSimpleSubgroups.range_le_of_normal`: generation
  inside a smooth connected closed normal subgroup `H` implies that `H`
  lies in any ambient closed competitor containing all ambient normal
  almost-simple subgroups. The proof uses the actual scheme-theoretic
  intersection with the competitor. The conditional normality-transfer
  theorem makes each internal normal factor normal in the ambient group.
- `range_eq_top_of_normal_and_centralizerCore`: a closed competitor
  containing `H` and the reduced identity component of its full centralizer
  is the whole semisimple group. Root dichotomy places each root functor
  in `H` or in the full centralizer. In the latter case its published smooth
  connected representative factors through that centralizer and then
  through the reduced identity component. Root generation gives fullness.

`isGeneratedByNormalAlmostSimpleSubgroups_of_actual_roots` proves the local
property by strong induction on the actual Lie dimension. If the identity
map has trivial range, every test-valued point is the identity and any closed
subgroup has full range. Otherwise the conditional minimal-factor
construction supplies a closed normal almost-simple subgroup `A`. Form its
full closed normal centralizer and the inclusion `n` of the centralizer's
reduced identity component `N` in `G`. The published action construction
gives all-test normality of `n`, and the centre premise gives semisimplicity
of `N`. If `n` were an isomorphism, its inverse would express every point of
`A` as a centralizer point, forcing `A` to be commutative on all tests,
contrary to almost-simplicity. Thus `N` has strictly smaller Lie dimension.
Induction gives generation inside `N`, intersection transport places `N`
in the competitor, and the centralizer-core helper gives its fullness.

`semisimpleAlmostSimpleGeneration_of_actualRoots` packages this result as the
exact published generation proposition, still with all three explicit
structural premises. Fullness and closed-immersion monicity make `d` a
representative of the full subgroup functor; the existing `topIso`
construction supplies the actual isomorphism and identifies its forward map.

The provenance is internal composition of the published actual subgroup,
root-representability, action, and Lie-dimension interfaces and the explicit
conditional reductions. Every normality, containment, and fullness assertion
uses every test scheme, including nonreduced tests. No smoothness,
connectedness, or normality of `D` is assumed. This construction proves
neither structural premise and does not supply an unconditional proof of
`SemisimpleAlmostSimpleGenerationStatement`.

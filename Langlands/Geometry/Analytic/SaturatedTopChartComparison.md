# Greatest-chart comparison and pullbacks in the saturated category

This internal construction retains the actual saturated presentations and all
bounded pullbacks of their complete strong maps. Its comparison results use
independent field, space and atlas-index universes `u`, `v`, `w`. The small
spectrum comparison and pullback construction specialize only the last two
universes to `v`; `u` and `v` remain independent. The coefficient field has
`NormedField`, `IsUltrametricDist` and `CompleteSpace` instances throughout.

A greatest chart means a specified chart whose range contains the range of
every chart of the presentation. The construction assumes these greatest
charts on the objects of the cospan. It imposes no greatest-chart assumption
on the source of a test cone.

## Complete maps and comparison

`asTopChart` regards a saturated presentation with a greatest chart as the
existing `TopChartPresentation`, retaining its whole atlas. `ofTopAlgebraMap`
uses the existing greatest-chart reconstruction to produce a complete strong
map from a bounded map of the greatest-chart algebras. The accompanying
pullback formula, inverse formula, `hom_ext_topAlgebra` and
`topAlgebraMapEquiv` identify the full strong Hom type with those bounded
algebra maps. The equality criterion concerns every stored pullback and the
ambient map.

`id_pullbackAtTop` computes the identity, and `topChartIsoOfAlgebraEq`
constructs a strong isomorphism from equality of the greatest-chart algebras.
Its inverse identities use actual saturated composition, its formula on
greatest-chart pullbacks, and the two inverse algebra transports.

`chartSpectrum_small` proves that every actual chart spectrum is small in
the ambient space universe, since its chart map is an embedding into the
ambient space. For a presentation with atlas-index universe `v`,
`smallSpectrumIso` consequently compares it with the saturated small actual
spectrum of its greatest-chart algebra. The forward map pulls the algebra
back by transport along the retained original-chart equality.

`smallSpectrumIso_naturality` proves that the small-spectrum map of the
bounded greatest-chart pullback followed by the target comparison equals
the source comparison followed by the original complete strong map.
The proof computes both composites on the greatest algebras, uses the
retention of original bounded maps under small-spectrum saturation, and
eliminates the two algebra equalities and the heterogeneous map equality.
The full-map equality criterion then proves the asserted naturality.

## Pullbacks of the original presentations

Fix complete strong maps `f : A ⟶ C`, `g : B ⟶ C` and greatest charts on
`A`, `B`, `C`. Let `φ` and `ψ` be their bounded greatest-chart pullbacks.
Assume that the actual spectrum of `AffinoidPushout.algebra φ ψ` is small
in `v`. `greatestChartPullback` is its saturated small actual spectrum.
Its projections are the small-spectrum pushout projections followed by the
comparison isomorphisms to the original `A` and `B`.

`greatestChartPullback_isPullback` transports the full strong universal
property of the small actual affinoid pushout along these comparisons.
The pullback vertex uses the identity isomorphism, and the other three
vertices use `smallSpectrumIso`. The four commuting comparisons are the
two projection definitions and the two naturality equations. Mathlib's
`IsPullback.of_iso` supplies the resulting full categorical pullback.

`refinedStrongPullback_of_strongIsPullback` applies to any strict strong
pullback in independent `u`, `v`, `w`: its lift, with the identity source
refinement, supplies refined strong existence, and its uniqueness supplies
complete strong joint uniqueness. Applying it to the constructed square
and then the localized descent construction gives
`greatestChartPullback_isRefinedStrongPullback` and
`greatestChartPullback_localized_isPullback`. The latter is universal for
all localized test objects and arrows, including fractions.

## Conditional finite existence and scope

`exists_greatestChart_finite_isPullback` and its localized counterpart
assume `AffinoidPushout.FiniteBanachPushoutStatement K` and
`φ.IsFiniteBanach`. The existing finite pushout spectrum smallness theorem
supplies the smallness needed above; both existence results retain the
original cospan objects and maps and keep the pullback in space and
atlas-index universe `v`.

This is a derived construction from the existing greatest-chart comparison,
small actual affinoid spectrum and its full pullbacks, and refined strong
localization descent. It transcribes no external theorem. The smallness or
finite hypotheses are explicit, and the construction assumes greatest
charts on the three cospan objects. It asserts no etaleness and does not
construct the unrestricted global etale pullback of
`LocalizedEtalePullbackStatement`.

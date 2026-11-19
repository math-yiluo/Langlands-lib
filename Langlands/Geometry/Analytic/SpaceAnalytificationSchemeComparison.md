# Comparison with the glued analytification of a separated scheme

The theorem
`Langlands.Analytic.SpaceAnalytification.spaceAnalytificationScheme.{u}`
proves the unchanged proposition
`Langlands.Analytic.SpaceAnalytification.SpaceAnalytificationSchemeStatement.{u}`.
For a complete, ultrametric, nontrivially normed field `K : Type u`, a scheme
`X : Scheme.{u}`, a locally finite type separated morphism `f : X ⟶ Spec K`,
and a supplied analytification `(Y, p)` of the algebraic space represented by
`X`, it constructs a homeomorphism
`localizedSpaceFunctor.obj Y ≃ₜ SchemeAnalytification.Space K f`. The
homeomorphism identifies the map of every affine chart inclusion with
`ι K f U` and sends each `rationalPoint p P₀ x` to the glued
`analyticRationalPoint` of the corresponding scheme point, for every finite
polynomial presentation `P₀` of `K`.

The construction first defines the map in the other direction. For an affine
open `U`, `chartRingPoint` is the test point whose scheme morphism is the
inverse coordinate isomorphism followed by `U.ι`. The equivalence
`schemeRingPointsEquiv` proves that this is the unique test point with that
underlying morphism. Naturality of the affine coordinate isomorphisms proves
`changeRing_chartRingPoint`, which identifies the restriction to a smaller
affine open with that open's chart point. The naturality field of
`IsAnalytification` makes
the associated continuous chart maps compatible with the gluing relation.
The quotient descent map `SchemeAnalytification.desc` then constructs the
continuous map `schemeComparison` from the glued scheme space to the
underlying space of `Y`.

The Yoneda morphism of `chartRingPoint` is the represented affine chart
inclusion. It is an isomorphism followed by an open immersion, hence is étale.
The `etale_map` field and `etaleOpenMap` make each `chartComparison` open.
`schemeComparison_image` writes the image of a set as the union of the chart
images of its chart preimages. The quotient topology and openness on charts
therefore prove `isOpenMap_schemeComparison`.

Separatedness makes the intersection of two affine opens affine, because
the diagonal is affine over the affine base. `chartIntersection_isPullback`
transports the scheme intersection square through the coordinate
isomorphisms, the over category, and the scheme Yoneda functor. The
`isPullback` field of the supplied analytification gives a categorical
pullback square in the localized analytic category. The lemma
`SaturatedAtlasPresentation.exists_point_of_isPullback` lifts chart points
with the same image to a point of the analytic intersection. Its two
projections and the identities `ι_localMap` identify their points in the
glued scheme space. This proves `injective_schemeComparison`. The
point-lifting input applies because the field, space and chart-index
universes are all `u`, exactly as in the target.

Surjectivity uses principal localizations of arbitrary affine test
algebras. `chartPointAlgHom` is the algebra map determined by a relative
point of an affine open. Taking its spectrum recovers the point followed
by the coordinate isomorphism, and changing the test algebra along it
recovers the original scheme point. For an affine test point `x` and a
prime of its test algebra `A`, `exists_localized_chart_factorization`
chooses an affine open containing its image, then a basic open through
the prime contained in the inverse image of that chart. The open
immersion lifting property factors the localized test morphism through
the chart. This gives `a : A` and a chart-coordinate algebra map to
`Localization.Away a`, with `x` and the chart point inducing the same
localized test point.

For a point of `Y`, `jointly_surjective` supplies an affine test point and
an analytic point `z` mapping to it. Apply the preceding factorization to
`center K P z`. The finite polynomial presentation makes `A` a finite
type `K`-algebra. Its principal localization is also finite type and thus
has a finite polynomial presentation. The principal-localization range
formula `AffineAnalytification.ImmersionComparison.range_baseMap_away`,
together with `center_mem_basicOpen`, lifts `z` to that localized
analytification. Naturality for the localization map and the
chart-coordinate map then shows that the original point of `Y` is the
image of a point of an affine chart. This proves
`surjective_schemeComparison`.

The rational-point computation retains the actual relative scheme
morphisms. `chartPointAlgHom_eq_affineAlgPoint` identifies the
chart-coordinate algebra map with the one used by
`SchemeAnalytification.affineAlgPoint`. The identity follows from
faithfulness of `Spec`, the spectrum formula for that coordinate map,
and `PointTopology.affineSchemePointEquiv_spec`; the coordinate-algebra
equivalence is the identity on the underlying global sections.

The seminorm of an affine analytic rational point is `a ↦ ‖φ a‖`, by the
evaluation character defining that point. The restriction formula for
`pointSeminorm` and `SeminormComparison.pointSeminorm_injective` therefore
show that `baseMap` sends an analytic rational point to the analytic
point of the composite algebra map. For a `K`-point `x` of `X`, use the
chosen affine chart `pointAffine` and its point `pointLift`. The identity
`openPointMap_pointLift` says that changing the chart point along its
coordinate map gives `x`. Applying naturality at the analytic point of
the identity of `K` now proves `schemeComparison_analyticRationalPoint`
for every presentation `P₀`.

`schemeComparisonHomeomorph` equips the continuous open bijection with
its inverse homeomorphism. The exact-target theorem takes its inverse.
The uniqueness of `chartRingPoint` supplies the required identity for
every test point with the specified chart morphism. The rational-point
identity follows from `schemeComparison_analyticRationalPoint` and
injectivity of the homeomorphism.

The source context is Conrad–Temkin, *Non-archimedean analytification of
algebraic spaces* (2009), Lemma 2.2.1 and Definition 2.2.2, printed p.7,
Definition 4.1.1, printed p.18, and the final discussion of §4.1 on
printed p.19 (registered source
`conrad-temkin-2009-nonarchimedean-analytification`). These explain
independence of the quotient chart and its compatibility with schemes
and Zariski opens. Berkovich, *Spectral theory and analytic geometry over
non-Archimedean fields* (1990), Theorem 3.4.1 and proof steps (2)–(3),
printed pp.63–64/PDF pp.77–78 (registered source
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`),
give the scheme construction by open affine gluing. Conrad, *Weil and
Grothendieck approaches to adelic points* (December 31, 2011), printed
p.19, proof of Proposition 5.11(3) (registered source
`conrad-2011-weil-grothendieck-adelic-points`), uses the compatibility
with the scheme case and rational points.

The chart-point, localized factorization, and comparison helpers in this
module are internal consequences of the Library's definitions, following
the implemented argument above. The proof imports localized
point-lifting, étale openness, and the affine seminorm and localization
range results by their Lean modules. It preserves the given target and
all its assumptions and quantifiers.

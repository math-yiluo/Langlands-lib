# Actual domain base change in the localized analytic category

This internal construction exposes the published quotient-category inverse-image
domain theorem for arbitrary morphisms in the localized category of analytic
spaces. It is geometric support for the compact quasi-étale comparison.

For any localized analytic morphism `f : X ⟶ Y` and any actual analytic domain
`D` of `Y`, `domainPreimage f D` has exactly the inverse-image subset under
`localizedSpaceFunctor.map f`. The domain condition follows from
`SourceCategory.isOriginalChartDomain_preimage`: the published Hom equivalence
represents every localized morphism by a quotient morphism, and its space functor
is the composite of the comparison functor with `localizedSpaceFunctor`.
No new geometric domain condition is assumed.

Inverse image preserves identity, composition, intersections, the whole space,
the empty domain, and inclusions. `domainPreimageOrderHom` packages monotonicity.
`domainPreimageMap` is the existing analytic restriction of `f` from its
inverse-image domain to `D`; its underlying map is the restriction of the
underlying continuous map of `f`.

The cone `domainPreimageCone` uses the actual inverse-image domain inclusion and
this restriction map. For a commuting cone with legs `a` and `b`, the equality
of composites shows pointwise that `a` lands in the inverse image. The published
image-only factorization theorem then constructs `domainPreimageLift`. Its first
triangle is the factorization identity. Its second triangle follows by
cancelling the monic inclusion of `D`. Cancelling the monic inverse-image domain
inclusion also proves uniqueness. Thus `domainPreimageIsLimit` and
`domainPreimage_isPullback` assert a categorical pullback against every localized
test object, with no restriction to strong morphisms or Hausdorff spaces.

Finally, inverse image along an isomorphism and its inverse defines
`domainPreimageOrderIso`. Its two inverse laws follow from the composition and
identity laws for domain inverse image. It preserves and reflects inclusion.

The construction allows arbitrary field, space and chart-index universes
`u`, `v`, `w`, over a complete ultrametric normed field. It uses no new external
source attribution and assumes no unproved Library proposition. It supplies
base change for analytic domain inclusions; general fibre-product
representability, quasi-étale composition and base-change stability, finite
Čech presentations and the cohomological comparison remain separate obligations.

# Field-valued point lifting along analytic open immersions

This internal helper supplies exact lifts of full
field-valued points along analytic open immersions, using the actual
analytic-domain restriction construction. It was written for the rational
inverse comparison of `SpaceAnalytificationRationalPointsStatement` and does
not prove that statement.

Let `K : Type u` be a complete ultrametric normed field and let `L : Type uL`
be any normed field with a normed `K`-algebra structure. Space and chart-index
universes `v`, `w` and the coefficient-field universe `uL` are independent
of `u`. No completeness, ultrametric or algebraic-closure hypothesis on `L`,
nontrivial valuation hypothesis on `K`, or Hausdorff hypothesis on the spaces
is added.

`OpenImmersionFieldPointLiftingStatement` records the following property:
for every analytic open immersion `f : U → V`, a full `L`-valued point
`p` of `V` lifts to a full `L`-valued point `q` of `U` whenever its ordinary
point belongs to the range of the underlying map of `f`. The equality
`localizedFieldPointFunctor.map f q = p` includes all the field point's
containing-chart evaluations, not only its ordinary projection.

## Implemented proof

`exists_fieldPoint_lift_domainι` first treats the actual canonical inclusion
of any analytic domain `D` of a localized space `Y`. An ambient full field
point whose projection lies in `D` restricts to the domain. The proof
replaces `Y` by its original saturated presentation, which changes no object
data in the constructed localization. `FieldPoint.restrictOriginalDomain`
retains exactly the ambient point's evaluations on the charts contained
in `D`. The published `fieldPoint_map_restrictOriginalDomain` theorem says
that mapping this restricted field point back to the ambient presentation
recovers the complete original field point. The `domain` and `originalDomain`
presentations use the same actual subspace atlas and inclusion; the
all-local-domain proofs are propositionally irrelevant. Thus this theorem
applies to the canonical localized `domainι` itself.

`openImmersionFieldPointLifting` proves the recorded property. By the existing
definition, `f` is an isomorphism `e` onto an open analytic domain, followed
by its canonical inclusion. A witness that the ordinary point of `p`
lies in the range of `f` places it in that open domain, since the domain
inclusion is the subtype inclusion. The domain theorem gives its full
field-point restriction. Applying the field-point functor to `e.inv`
then gives `q`. Functoriality and `e.inv_hom_id_assoc` show that its image
is exactly `p`.

`localizedFieldPointProjection_map_down` records naturality of the existing
projection to ordinary points. It evaluates the actual naturality equation
of `localizedFieldPointProjection L` on a full field point, then removes
the `ULift`. It applies to every analytic morphism.

Finally, `exists_fieldPoint_lift_at_openImmersion` retains a prescribed
ordinary source point `x` whose image is the projection of `p`. Apply the
proved lifting theorem to obtain `q`; naturality identifies the image of
its projection with that of `x`. The underlying map of an analytic open
immersion is an open embedding and hence injective, so the projection of
`q` is exactly the prescribed `x`. No uniqueness of full field points is
needed or asserted in this argument.

## Provenance and scope

This is an internal deduction from the published `FieldPointDomains`,
`FieldValuedPoints`, `AnalyticImmersion` and analytic-domain constructions.
It translates no additional external mathematical statement. The theorem
concerns actual analytic open immersions and exact full field-valued point
maps. It proves no lifting theorem for general étale maps, no residue-field
descent, and no local-isomorphism theorem for étale maps at rational points.

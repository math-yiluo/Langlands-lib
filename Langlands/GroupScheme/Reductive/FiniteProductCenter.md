# Trivial centres of finite products and their factors

This internal helper supplies the adjointness transfer needed when a
split pinned chart is expressed as an actual finite product of
almost-simple factors. It is motivated by Brian Conrad, *Reductive
group schemes* (2014), Remark 6.4.5 and the proof of Proposition 6.4.4,
pp.232–233, registered as `conrad-2014-reductive-group-schemes`.

For a finite family of group schemes over any base scheme, a point of the
categorical product belongs to its full scheme-theoretic centre exactly
when every coordinate is central. The proof uses the multiplicative
finite-product point comparison. To test one coordinate, it inserts the
test point into that coordinate and puts identity points into the other
coordinates. Conversely, coordinatewise commutativity detects
commutativity in the product. Both directions retain every restriction
of the relative test scheme.

`centerPiPointsEquiv` packages this comparison as a multiplicative
equivalence between the centre point group of the product and the family
of centre point groups on every actual relative test scheme.

Consequently the full centre of the product is trivial if and only if
each factor's full centre is trivial. The same argument for a supplied
group isomorphism gives `center_factor_eq_bot_of_productIso`.
`center_eq_bot_of_iso` exposes the arbitrary-base isomorphism transport
used here.

`isAdjoint_geometricFactor_of_productIso` applies the resulting trivial
relative centre to every geometric fibre. Almost-simplicity supplies
semisimplicity of that fibre, so the result is adjoint. This proves the
actual fibre predicate, including the full possibly non-smooth centre,
without rational-point or reduced-centre substitutions.

These are internal consequences of the Library's full-centre predicate,
finite-product points and arbitrary-base preservation of a trivial centre.
There are no smoothness, reductivity, affineness or nonempty-index
hypotheses on the product-centre comparisons. All schemes, groups and
indices lie in the arbitrary universe `u`.

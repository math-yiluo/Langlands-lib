# Pointed refinements and equalization in the quasi-étale site

## Exact results

`QuasiEtaleSite.geometricPointRefinement` and
`QuasiEtaleSite.geometricPointEqualization` prove the published propositions
`QuasiEtaleSite.GeometricPointRefinementStatement` and
`QuasiEtaleSite.GeometricPointEqualizationStatement`. They use the actual
localized quasi-étale site over an arbitrary base `X` and full `L`-valued
points, with the ground field, analytic space, and point field universes
independent as in the statements. There is no compactness or separation
hypothesis on `X` or the source spaces of the original site objects.

## Implemented proof

- **Pointed charts.** In a strong representative of a quasi-étale arrow, the
  ordinary point lies in the finite union of the chart domains provided by
  `exists_local_domainEtale_charts`. Choose a member containing it. Lift the
  full field point to that domain, and transport back to the original arrow
  along its arrow isomorphism. This gives a compact chart domain mapping into
  the original source by a domain embedding; its map to `X` has a single
  domain–étale factorization. That factorization makes the chart an object of
  the same site.
- **Common refinement.** Choose such a chart for each point. The charts have
  an analytic fibre product over `X`. The product's common map to `X` has a
  domain–étale factorization by `HasDomainEtaleFactorization.of_isPullback_common`
  (a domain of the product of the two étale envelopes). The points restricted
  to the charts still have equal full images over `X` by functoriality.
  Preservation of the pullback by the field-point functor gives a point on
  the product. Compose its projections with the chart inclusions.
- **Equalization.** Choose a pointed chart of the source and a compact chart
  in the target through the common image point. Inside the source chart,
  intersect the inverse images of the target chart under the two maps. This
  is an analytic domain containing the point and both maps there factor
  through the target chart. Their images there are the *same full field
  point*: the map on field points of the target chart inclusion is injective.
  The two factorizations still agree after mapping to `X`. Into the
  self-pullback of the target chart over `X`, their pair and the diagonal
  agree at the corresponding field points, by uniqueness in the pullback of
  types. The target chart is compact, so its diagonal is an analytic-domain
  embedding by `compactQuasiEtaleDiagonalDomain`. Restrict to the inverse
  image of that domain; it contains the chosen point and the two maps now
  agree. The two successive restrictions preserve the source chart's
  domain–étale factorization over `X`, so the last restricted space is a
  valid site object. Mapping its lifted point back through the two domain
  inclusions and the source chart recovers the prescribed point.

These are the two cone inputs of the published cofilteredness reduction
`pointFibre_isCofiltered_of_geometry`. The proof uses charts rather than
assuming global quasi-étale composition, base change, or right cancellation.
It does not assert the covering-lifting input or the full point axioms.

## Provenance

Berkovich, *Vanishing cycles for formal schemes*, Invent. Math. **115**
(1994), §3, printed pp. 543–544, defines the quasi-étale site and records its
stability properties. The results here are derived statements about the full
field-point functor of the Library site. The proof uses local factorizations,
products of étale envelopes, and diagonals of compact charts, not a Lean
assertion of all the stability clauses of Berkovich's Lemma 3.1.

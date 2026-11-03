# The least closed subgroup containing every ground-field torus

Worker 1333. This internal adapter uses the fixed `closedTorusEnvelope` and
`TorusGeneratedEnvelope` from `Rational.TorusGeneratedEnvelope`. The field and
universe are arbitrary.

`IsTorusGeneratedSubgroup i` is a proposition about an actual homomorphism
`i : H ⟶ G`. It requires closedness, containment of every closed ground-field
torus, and leastness among actual closed subgroups having that containment
property. Both containment and leastness use `SubgroupFunctor.range` on every
scheme over the ground field, with the unchanged `ContainsTori` predicate.
They are not assertions about generation of a single group of rational or
geometric points.

`range_eq_closedTorusEnvelope` proves equality with the existing fixed envelope.
The leastness field gives containment in each subgroup in the defining
intersection, and the envelope's minimality gives the reverse containment.
Closedness supplies the underlying monomorphism, so `represents` obtains the
existing `IsRepresentedBy` predicate. Conversely, a closed representative of
the envelope contains every torus and is least by the envelope's two elementary
properties. `isTorusGeneratedSubgroup_iff` proves precisely this equivalence.

`toEnvelope` packages the same inclusion as `TorusGeneratedEnvelope` data.
`range_eq` gives same-image uniqueness; `iso` and `iso_hom_comp` reuse the
existing uniqueness of representatives to construct an actual source
isomorphism compatible with the inclusions into `G`.
`TorusGeneratedEnvelope.isTorusGeneratedSubgroup` provides the converse adapter
for any supplied representative.

The provenance is internal: these are direct consequences of the published
intersection and represented-subgroup interfaces. The structural motivation
for that existing envelope is recorded in its paired Markdown. This adapter
asserts no existence, normality, smoothness, connectedness, or rational density
theorem. Those properties require separate proofs.

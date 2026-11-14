# Étaleness of open analytic domains

`Langlands.Analytic.SaturatedAtlasPresentation.EtaleOpenDomainStatement X`
asserts that the canonical inclusion of every open subset of the analytic
space `X` is étale.

The objects and morphisms are the existing `openDomain`, `domainObj` and
`domainι` constructions from `InvariantAnalyticDomains`. The predicate
`etale` is the published definition using an arrow isomorphism to a strong
map between constructed saturations that is étale over all affinoid pieces.
The statement retains the field and universe parameters of `EtaleSite`;
it adds no Hausdorffness or field-valued-point hypothesis.

This is an internal prerequisite for the analytic étale compact-support
comparison, not a supplied proof. In a Hausdorff space it makes the open
complement of a point an object of the étale site. Covering by that
complement and an étale neighborhood then lets the point axioms lift any
field-valued point into the neighborhood whenever its underlying point
belongs to the neighborhood's image.

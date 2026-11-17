# Ordinary-open fibers and actual analytic point products

This internal coordinate prerequisite works with the actual analytic étale
points and canonical open analytic domains, keeping the space and coefficient
universes independent.

An open-domain object is subterminal in the étale site: its maps from any fixed
object are unique by the analytic-domain universal property. Its structural
arrow to the terminal identity object is therefore monic. Left exactness of an
actual site-point fiber then implies that its fiber over the domain has at most
one element.

Any such lift projects into the defining ordinary open, by naturality of the
actual point projection and the literal subspace inclusion formula. Conversely,
on a Hausdorff base the published point-lifting theorem supplies a lift whenever
the point projection lies in the open. This gives `openEtaleFiberEquiv` from the
actual analytic point fiber to the standard ordinary-topology point fiber. The
identification is compatible with ordinary-open restriction maps.

`ordinaryFieldPointFamily` indexes the standard ordinary-topology points by the
original field-valued points and places each at its actual point projection.
For an arbitrary independent module coefficient family, the proved fiber
equivalence reindexes the existing analytic point-product section coordinates
into the existing ordinary point-product coordinates. The coordinate formula
and restriction compatibility are proved. `openPointProductSheafIso` lifts
this comparison to an isomorphism of the actual module sheaves: ordinary
restriction of the raw analytic point product is the product of ordinary
skyscrapers at these projected points. Multiple field-valued points over the
same underlying point retain their independent coefficients.

These are internal consequences of existing domain monicity, actual point
fibers and point lifting; no new original-literature claim, smoothness assertion
or higher-cohomology vanishing is assumed.

# Ordinary higher direct images of actual analytic point products

This internal prerequisite proves a local-acyclicity result for the existing raw
point product on the actual analytic étale site. It does not apply a locally
discrete coreflector. The category and coefficient universes are independent:
`X` has atlas levels `u`, `v`, the coefficient level is
`W = max u (v + 1) uL`, and the coefficient index and point fibers use `W`.
The site-point family is arbitrary. The construction section displays the
sheafification, local-smallness, ordinary-direct-image additivity, finite-limit
preservation and (for the ordinary injective resolution) injective-preservation
instances explicitly; all are provided by existing analytic theorems.
No Hausdorff, point-surjectivity or action
hypothesis is used.

`coefficientPointProduct_underlying_preservesEpimorphisms` proves that the
existing raw coefficient product followed by the actual ordinary direct image
`etaleUnderlyingSheaf` preserves epimorphisms of coefficient diagrams. Ordinary
open sections are literally the original sections on the corresponding analytic
open domain. The existing coefficient-product sectionwise lifting theorem
therefore gives surjectivity on every ordinary-open section module. Componentwise
epimorphy, and reflection by the faithful sheaf inclusion, give epimorphy of the
ordinary sheaf map. Left exactness of both functors and additivity then give
`coefficientPointProduct_underlying_preservesHomology`.

`etalePointProductUnderlyingInjectiveResolution` maps a coefficient-diagram
injective resolution through that exact composite. The raw point product sends
injective coefficient diagrams to injective étale sheaves; the proved flat
ordinary/étale site adjunction makes ordinary direct image preserve injectives.
Thus all its terms are injective ordinary sheaves, and exactness gives the
augmentation and resolution property via the existing `mapInjectiveResolution`.

`isZero_etaleUnderlyingHigherDirectImage_coefficientPointProduct` proves all
positive actual ordinary higher direct images of a raw point product vanish,
even for arbitrary coefficient diagrams. It uses the coefficientwise injective
resolution of the raw étale sheaf. Applying actual ordinary direct image gives
precisely the complex obtained by applying the exact coefficient composite to
the coefficient injective resolution. This complex is exact in positive degrees.
Its homology computes the existing `etaleUnderlyingHigherDirectImage`, so the
claimed object is zero. The final
`isZero_etaleUnderlyingHigherDirectImage_pointProduct` theorem installs the
already proved analytic instances, giving the same conclusion without any
additional categorical-instance hypotheses on the caller.

The argument reuses the actual point product, site adjunction, right-derived
functors and injective resolutions. It uses no unproved Library proposition or
equivariant cohomology comparison. This is an internal categorical derivation.
Vanishing after the locally discrete coreflector remains a distinct local
analytic obligation for the Godement target.

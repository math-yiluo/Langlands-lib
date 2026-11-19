# Quasi-étale recognition from analytic-domain restrictions

`HasLocalDomainEtaleFactorizations f` asks for a finite family of analytic
domains through each source point. Their union is a neighbourhood, and each
restriction of `f` factors through an analytic-domain embedding into an
étale space over the target. The definition uses the actual localized
domain inclusions in the independent field and space universes of
`quasiEtale`.

An analytic-domain embedding identifies its source with an actual analytic
domain of the target by an isomorphism in the localized category. At any
point of the source, the proof constructs finitely many charts whose union
is a neighbourhood of that point. Each chart maps to an affinoid domain of
the target.

The isomorphism to the domain is represented by a fraction with two strong
quasi-isomorphism legs. Charts near the corresponding point of the common
source have actual chart images along both legs. The isomorphisms on these
chart domains respect their inclusion maps, so the composite into the
target is the inclusion of an affinoid domain after an isomorphism. The
denominator homeomorphism carries the neighbourhood to the original source.

To recognize a quasi-étale arrow, transport the finite domain families to a
strong representative using inverse-image domains. On each member, the
chart refinement gives a relative neighbourhood of the point. The charts
of the domain come from ambient charts and the nested-domain comparison
retains their full inclusion maps. Intersecting the finitely many ambient
neighbourhoods that lift the relative ones gives a neighbourhood covered by
the resulting ambient charts. Each chart has an affinoid-domain embedding
into an étale envelope over the target, which gives `IsQuasiEtale` for the
strong representative.

For a Hausdorff source, a quasi-étale arrow also has the local
factorizations. The compact charts of its quasi-étale strong
representative are closed. Removing the finitely many charts missing the
point preserves a neighbourhood, and the arrow isomorphism transports the
remaining domains and their étale factorizations.

The definition and the recognition proofs are internal consequences of the
Library's localization, analytic-domain and quasi-étale predicates.

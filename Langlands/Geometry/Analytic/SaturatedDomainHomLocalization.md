# Quotient morphisms under localization of actual domains

This derived unit identifies the two actual quotient-category realizations of
a domain inside an original-chart domain. It then identifies their presheaves
of all quotient morphisms into any fixed saturated target. The input is the
existing constructed category and its proved image-only domain universal
property. No strong representative or global gluing output is supplied.

The source motivation is Berkovich, *Étale cohomology for non-Archimedean
analytic spaces* (1993), Definition 1.3.1 (printed p.23 / PDF p.20) and
Proposition 1.3.2 (printed p.24 / PDF p.21). The registered original is
`berkovich-1993-etale-cohomology`, SHA-256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
The definition gives the image-only universal property of analytic domains;
the proposition supplies the broader morphism-descent motivation. The present
result is derived infrastructure for the original-chart model, rather than
a claim that this model already describes all analytic spaces and domains.

Let `S` be an actual domain of `A` and `U` an actual domain of the induced
subspace presentation on `S`. The previously constructed `S.subspaceExtend U`
is the ambient image of `U`; its carrier is literally `Subtype.val '' U`.
The earlier localization order isomorphism proves that this is again an
actual original-chart domain.

`domainNestedMap` maps the ambient-image realization to the nested one.
The arrow from the ambient-image domain to `S` is `domainMap`; its point image
lies in `U` because forgetting intermediate membership is the identity on
ambient values. Apply the proved domain universal property to this arrow.
`domainNestedMap_inclusion` is the resulting factorization equality.

`domainNestedInverse` factors the double inclusion of `U` into `A` through
the ambient-image domain. Its image witness is the actual point of `U`.
`domainNestedInverse_ambientInclusion` records that factorization.
Cancelling the monic inclusion of `S` also gives
`domainNestedInverse_map`, the factorization into the intermediate domain.
These two triangles and monicity of the actual domain inclusions prove both
inverse laws of `domainNestedIso`. All equations hold for complete arrows
of the source quotient, whose representatives retain bounded algebra maps.
The pointwise formulas are consequences of these constructed factors; point
values are not used as a faithfulness principle.

For an inclusion `U ≤ V`, compose the two candidate comparison squares with
the inclusion of `V` into `S`. The factorization triangles and `domainMap_comp`
give the same arrow, so monicity proves `domainNestedMap_naturality`.
`domainNestedNatIso` packages the isomorphisms as a natural isomorphism
between ambient-image realization and nested realization. The same
cancellation into `A` proves `domainNestedInverse_naturality`.

Precomposing with the inverse comparison gives `domainHomNestedEquiv`.
Its inverse precomposes with the forward comparison, and the two inverse
laws follow by associativity and the proved isomorphism laws. Applying the
inverse-comparison naturality square to each quotient arrow proves
`domainHomLocalization`: the quotient-Hom presheaf on `S` is naturally
isomorphic to the ambient quotient-Hom presheaf pulled back along the
actual domain-extension functor. `domainHomLocalization_hom_app` gives the
explicit component, and `domainHomLocalization_postcomp` proves compatibility
with arbitrary quotient target arrows by associativity.

The field, ambient-space and chart-index universes are independent. All
domains, including empty ones, are allowed. The result constructs transport
for arbitrary quotient morphisms; it does not prove the existence of gluing
for arbitrary matching quotient families. That existence, full analytic
identification, and the étale and equivariant site constructions remain open.

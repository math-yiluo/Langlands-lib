# Isometric idempotence of weighted rational intersections

Author: Worker 56.

This module constructs the actual bounded algebra equivalence between the
all-products quotient for the intersection of a rational presentation with
itself and the original rational quotient. It imports the published
`GeneralizedAffinoid.RationalIntersection` construction and does not change
its coefficient algebra, rational relations or quotient norms.

Work over a complete ultrametric normed field `K` and an actual
`A : PresentedAffinoidAlgebra K`. Let `s` be any finite positive polyradius,
`g` a scalar-series denominator and `f` the scalar-series numerator tuple.
Put `B = RationalPresentation.algebra K A s g f` and
`D = RationalIntersection.Algebra K A s s g g f f`. Thus `D` has denominator
`g * g`, all products of the extended tuple `(g, f)`, and the products of the
extended radii `(1, s)`. Both carriers and norms are the existing closed
quotients.

The tuple `collapseTuple` in `B` assigns a product coordinate `(i,j)` the
product `u_i * u_j`, where `u = (1, fraction)`. Coordinate bounds and
`‖1‖ ≤ 1` give the product-radius bound. The fraction equations give
`b(g²) * u_i * u_j = b(v_i * v_j)`, with `v = (g,f)` and `b` the actual
coefficient map. The monomial bound then permits contractive evaluation of
the intrinsic relative rational quotient. Composing this evaluation with the
published isometric scalar/relative comparison constructs
`collapseMap : D → B`. It fixes coefficients and sends every product
coordinate to the stated product. It sends both the left and the right
coordinate to the original fraction. Construction of this map and its
contractivity do not require unit generation.

For `hf : GeneratesUnitIdeal K A g f`, the existing left restriction
`leftMap : B → D` supplies the inverse. Unit generation also holds for the
product presentation. Published denominator-unit extensionality shows that
both composites are identity maps because they fix every coefficient.
The same extensionality proves `leftMap = rightMap` for this repeated
intersection. The constructed `idempotentEquiv : BoundedAlgEquiv K D B`
therefore has inverse the actual left restriction, also equal to the right
restriction. Contractivity in both directions proves exact equality of the
two quotient norms and an isometry. No inverse, norm equality or universal
property is assumed.

`idempotentSpectrumHomeomorph` is the actual contravariant homeomorphism
`BanachSpectrum B ≃ₜ BanachSpectrum D` induced by this equivalence. Its
forward action is seminorm precomposition with `collapseMap`; its inverse
uses `leftMap`. It commutes with structural pullback to `BanachSpectrum A`.
Composing either restriction spectrum map with this homeomorphism is the
identity on `BanachSpectrum B`.

The result retains empty numerator tuples, arbitrary positive real radii,
trivial valuations, nilpotents and zero quotients. Unit generation is an
explicit hypothesis of the equivalence and inverse identities. Completeness
of `K` is required for convergent evaluation and the scalar/relative
comparison; the elementary tuple bounds and equations precede this
hypothesis. No normalization `‖1‖ = 1` is used.

This is an internal derivation from the published weighted rational and
product-intersection constructions. Its source context is Berkovich,
*Non-Archimedean analytic spaces*, Trieste lectures (2009), registered as
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`,
Definition 2.1.6(i), page 8, and Exercise 2.2.2(ii),(iii), page 9. Those pages
describe weighted relative series, rational quotients and intersection
stability. The explicit repeated all-products presentation and exact
quotient-norm isometry are derived here, rather than quoted as a separate
source theorem. Printed and PDF page numbers agree; pages 8–9 were read and
no source-specific errata note was present in the current Library.

This construction does not supply the general bounded-pushout theorem or the
comparison with a newly iterated intrinsic quotient. Full affinoid-domain
factorization from arbitrary spectral-image containment, analytic atlases,
structure sheaves, analytic sites and the Harris tower remain separate
obligations.

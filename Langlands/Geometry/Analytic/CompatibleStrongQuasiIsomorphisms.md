# Full quasi-isomorphisms and actual saturation

This module is an internal consequence of the actual bounded-map
constructions in `CompatibleStrongOriginalRestriction`, the full-domain
composition and factorization lemmas in `StrongQuasiIsoComposition` and
`GeneralizedAffinoid.RationalChartDomainComposition`, and the existing
saturated quasi-isomorphism composition. It works over a complete
ultrametric normed field, allowing trivial valuation. Original
presentations have ambient universe `v` and arbitrary chart-index
universe `w`; their constructed enlargements have chart-index universe
`v`. The original compatible maps use the explicit local-domain
compatibility law of `CompatibleStrongMaps`.

The quasi-isomorphism condition is the existing `StrongHom.IsQuasiIso`:
the continuous base map is a homeomorphism, and at every admissible
original chart pair its actual bounded pullback represents the relative
chart-image locus. Representation includes unique bounded factorization
over every presented affinoid test algebra.

`PresentedAffinoidAlgebra.represents_range_iff_of_heq` transports this full
representation of the actual spectrum range along equalities of the
presented source and target algebras and heterogeneous equality of the
entire bounded maps. Its proof eliminates these equalities; it uses no
reconstruction from spectrum data.

For an original strong quasi-isomorphism `f`,
`IsQuasiIso.represents_localChartPullback` proves full representation for
the already constructed map from any source local domain `U` to every
original target chart containing its image. First use the chosen target
of `U`'s original parent. The parent pullback represents its image by the
quasi-isomorphism hypothesis. Compose it with `U.domain.baseMap` by
`Represents.comp_of_injective`, using the embedded parent spectrum map.
The actual chart square and the spectrum image of `U.domain.baseMap`
identify this image with `f.baseMap '' U.locus`. The existing
`represents_changeMapChart` theorem then transfers the full representation
to the requested target chart.

`IsQuasiIso.represents_localDomainPullback` further factors this map
through any full target local domain `V` containing the image.
`localDomainPullback_comp_baseMap` identifies the full bounded composite.
`Represents.of_comp_of_injective`, applied to `V.domain.represents` and
its embedded spectrum map, proves that the actual local-domain pullback
represents the inverse image of `f.baseMap '' U.locus` under
`V.ambientMap`. This step retains unique factorization on all affinoid
tests.

`IsQuasiIso.saturationExtension` adds the coefficient-coherence hypothesis
needed to form the existing actual extension. Its continuous base map is
unchanged. For every enlarged pair, use the preceding theorem on the
chosen source and target representatives; their proved ambient-map
ranges identify the resulting locus with the enlarged relative
chart-image locus. Thus the extension is a full quasi-isomorphism.

Conversely, `IsQuasiIso.originalRestriction` starts with any full
quasi-isomorphism between the two constructed enlargements. For each
original admissible chart pair, the two original enlarged charts are
admissible. The existing original-pullback transport identifies the full
bounded maps heterogeneously and identifies their actual presented
endpoints. Apply `represents_range_iff_of_heq` to the enlarged
representation, using `range_pullback` to identify each representation
locus with its actual spectrum range. The unchanged base map retains the
homeomorphism. This proves the original restriction is a full
quasi-isomorphism.

For a compatible original map,
`CompatibleStrongHom.isQuasiIso_saturationExtension_iff` combines
preservation with reflection and the complete original-restriction
recovery law. `isQuasiIso_comp` extends two original compatible maps,
uses full quasi-isomorphism composition in the constructed saturated
category, and reflects the result back. The actual extension-composition
equality identifies this result with the original compatible composite.

`CompatibleAtlasPresentation.quasiIsomorphisms` is the morphism property
on the existing original compatible category defined by this full
condition. Its `IsMultiplicative` instance uses the existing identity
quasi-isomorphism and the just-proved original composition result.
`quasiIsomorphisms_saturationFunctor_map_iff` states that the actual
saturation functor preserves and reflects precisely this property.

These results compare actual bounded-map morphism classes. They do not
require equality of the original and ambient index universes. The
analytic localization and its comparison with the saturated localization,
etale and quasi-etale sites, equivariant constructions, compact and
distinguished domains, and Harris tower specializations remain subsequent
obligations.

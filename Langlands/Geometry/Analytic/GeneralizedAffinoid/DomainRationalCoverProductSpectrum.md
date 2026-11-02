# Actual spectrum pullback of a mixed finite-cover product

## Setting and construction

Work over a complete ultrametric normed field `K`, a presented affinoid algebra
`A`, and a full represented domain `U : Domain K A`. The inputs are a finite
full-domain cover `c : FiniteCover U` and a supplied finite rational cover
`r : FiniteRationalCover U`. The imported `c.rationalProduct r` retains the
actual rational coefficient-pullback quotient for each pair of component
indices. Its two refinement projections retain their actual bounded algebra
restrictions.

`FiniteCover.TotalSpectrum` abbreviates the finite disjoint union

```
Σ i : Fin c.size, BanachSpectrum (c.obj i).algebra.
```

Each component carries its actual Banach-spectrum topology, and the sum carries
the disjoint-union topology. The existing continuous `c.totalMap` has target
`U.locus`, with its subspace topology in `BanachSpectrum A`.

`c.RationalProductSpectrumFiber r` is the subtype of
`c.TotalSpectrum × r.toFiniteCover.TotalSpectrum` consisting of pairs `(x, y)`
with equal images under the two original total cover maps. It carries the
subspace topology from this product. `c.rationalProductSpectrumComparison r`
sends an actual product-component spectrum point through both bounded
projection restrictions, retaining both output component labels. The imported
total-map triangles prove compatibility, and the two continuous projections
prove continuity into the subtype.

## The comparison is a homeomorphism

`rationalProductSpectrumComparison_injective` first compares the labels of both
output sigma points. The finite pair-index equivalence identifies the original
product-component labels. In that common component, equality of the first
projection identifies the points: this projection is the spectrum map of the
pulled rational chart, whose spectrum/locus homeomorphism has already been
constructed. No injectivity of an arbitrary full domain is used.

`rationalProductSpectrumComparison_surjective` starts with a compatible pair of
actual points, labelled by an original cover component and a rational chart.
Equality in `U.locus` implies equality of their ambient spectrum images. The
first point therefore lies in the inverse-image rational locus. Applying the
pulled rational chart's inverse locus homeomorphism gives a point of the actual
coefficient-pullback quotient spectrum. Its first projection is the given first
point. The bounded projection triangles give equality of the second projection's
ambient image with that of the given rational-chart point; the rational chart's
locus homeomorphism identifies these points. The pair-index equivalence places
this lift in the required component of the total product spectrum.

`c.rationalProductSpectrumHomeomorph r` upgrades this continuous bijection to a
homeomorphism. The source is compact because it is a finite disjoint union of
compact actual affinoid spectra. The target is Hausdorff because it is a subtype
of a product of Hausdorff sums of spectra. Thus the continuous comparison is a
closed map, and its inverse is continuous. The `_fst`, `_snd`, `_symm_fst` and
`_symm_snd` lemmas identify both projections of the homeomorphism and its inverse
with the actual spectrum maps of the refinement projections.

## Continuous lifting and the topological pullback

`c.rationalProductSpectrumLift r f g h` accepts continuous maps from any
topological space into the two original total spectra and a pointwise equality
of their images in `U.locus`. Pairing these maps gives a continuous map into the
compatible-pair subtype; composing with the inverse homeomorphism constructs a
continuous lift into the actual mixed-cover total spectrum. The `_fst` and
`_snd` lemmas prove the two factorization equations as equalities of continuous
maps.

`c.rationalProductSpectrumCone r` is a `TopCat` pullback cone over
`TopCat.ofHom c.totalMap` and `TopCat.ofHom r.toFiniteCover.totalMap`. Its vertex
is the actual total spectrum of `c.rationalProduct r`; its two legs are induced
by the actual bounded restrictions of `c.rationalProductFst r` and
`c.rationalProductSnd r`. The `_pt`, `_fst` and `_snd` lemmas specify these data.

`c.rationalProductSpectrumConeIsLimit r` proves the cone's limit property. For
any competing cone, its commuting equation gives the pointwise compatibility
required by `rationalProductSpectrumLift`. The continuous-map projection lemmas
prove both factorizations. Any competing lift with those factorizations has the
same two projections; injectivity of the comparison proves equality pointwise,
hence equality of the `TopCat` morphisms. This constructs the pullback universal
property for all competing topological spaces, not only affinoid test spaces.

## Provenance and scope

This is an internal consequence of the published actual rational coefficient
base-change construction, the supplied covers, and their actual common
refinement. The source context is Vladimir G. Berkovich, *Non-archimedean
analytic spaces* (Trieste lectures, 2009), registered as
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`:
Definition 2.2.1 and Exercise 2.2.2(ii)–(iii), printed/PDF p. 9, supply the full
affinoid-test domain representation, positive-radius rational quotient and
intersection context; Definition 2.2.7, printed/PDF p. 10, supplies the
domain-embedding category. The chosen-index disjoint-union homeomorphism and
`TopCat` limit are derived here rather than attributed to a numbered source
assertion. The Lean proof uses the already proved rational-chart homeomorphisms,
not the unrestricted domain-spectrum homeomorphism of Fact 2.2.3(i).

Empty covers and empty loci, arbitrary finite positive polyradii, and trivial
valuations are permitted. Neither the target full domain nor the full-domain
cover components are assumed to have injective structural spectrum maps. The
rational cover is supplied; the existence theorem of Fact 2.2.5 is not proved.
This module does not construct arbitrary full/full base change, analytic atlases,
structure sheaves, Tate acyclicity, etale or quasi-etale sites, equivariant sites,
or Harris's tower. Those remain separate obligations of the analytic branch.

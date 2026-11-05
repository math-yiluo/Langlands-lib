# Actual inverse-image domains and pullback squares

This module proves that every morphism in the source-quotient category of
saturated atlas presentations pulls an original-chart domain back to an
original-chart domain. It constructs the domain on that literal subset, the
map to the target domain, and a limiting pullback cone for the two ambient
arrows. All four arrows are actual analytic morphisms of the constructed
category.

The coefficient field `K : Type u` is complete, normed and nonarchimedean.
The underlying spaces and chart indices have independent universes `v` and
`w`. The imported full affinoid-domain tests use positive-polyradius presented
affinoid algebras, without reducedness or strictness assumptions. No ambient
Hausdorff assumption is added.

## Source and scope

The source is Berkovich, *Étale cohomology for non-Archimedean analytic spaces*
(1993), registered as `berkovich-1993-etale-cohomology`, Definition 1.3.1 and
the paragraph immediately following it, printed p.23 / PDF p.20. The
definition uses finite relative neighborhoods of contained affinoid domains.
The following paragraph asserts stability under intersections and inverse
images, constructs the contained-domain atlas and inclusion, and gives the
image-only unique factorization property.

This is a derived implementation of the inverse-image assertion in the
current locally saturated model. `OriginalChartDomain` uses contained
original charts and their finite relative neighborhoods. Saturation asserts
closure under every full local affinoid domain of such a chart. The
source-quotient category retains complete bounded pullback families, with
equality on a common locally refining source subatlas. These constructions
do not yet identify this model or its domains with the full analytic-space
category and maximal atlas of the literature. The pullback assertion below
is derived from the implemented inverse-image theorem and the already
constructed image-only domain factorization.

## Inverse images before source localization

For a full strong map `f : A ⟶ B` with saturated source atlas,
`StrongHom.originalCharts_refine_domainPreimage_chart` proves that the
original source charts locally refine

```text
range (A.atlas.chart i) ∩ f.baseMap ⁻¹' S.carrier.
```

Choose an admissible target chart `j` for `i`. The intersection of the target
domain `S` with the range of `j` is an original-chart domain. Its finite
relative neighborhoods give a finite family of contained target charts,
each containing the image point. Intersect their inverse images with the
fixed source chart. The existing full affinoid inverse-image construction
and source saturation realize each resulting subset as an actual original
source chart. Continuity on the displayed intersection pulls the finite
relative target neighborhood back to a finite relative source neighborhood.
This proves the required chartwise local refinement without assuming any
atlas on the inverse image.

`StrongHom.isOriginalChartDomain_preimage` first uses the ambient source
quasinet to refine the full inverse-image subset by intersections with
original source charts. Restricting the finite ambient neighborhoods to the
inverse-image subset proves this refinement. Composition with the previous
chartwise refinements proves the global original-domain predicate.

## Descent and literal domain inverse image

`SourceCategory.isOriginalChartDomain_preimage` applies quotient induction
to an arbitrary arrow `F`. A representative consists of a locally refining
original source selection `P` and a complete strong numerator `f`.
`spaceFunctor_map_ι` identifies the underlying continuous map with exactly
`f.baseMap`, since the denominator's continuous map is the identity on the
original ambient space. The strong inverse-image theorem applies to the
saturated refining subpresentation. The existing
`isOriginalChartDomain_subatlas_iff` then transports that domain predicate
back to the original atlas.

`domainPreimage F S` bundles the literal subset
`spaceFunctor.map F ⁻¹' S.carrier` with this proof. `mem_domainPreimage` is
the exact membership formula. The identity and composition laws follow from
the corresponding laws for the literal-space functor. Inverse image also
preserves intersection, the whole domain and the empty domain, by equality
of the underlying subsets. `domainPreimageOrderHom F` packages its
monotonicity.

## The actual base-change square

Write `P = domainPreimage F S`, `incP = domainInclusion A P`, and
`incS = domainInclusion B S`. The domain objects are the previously
constructed saturated subspace presentations, with their contained original
algebras and all bounded restrictions.

`domainPreimageInclusion_comp_image` proves that `incP ≫ F` has image in
`S`. `domainPreimageMap F S` applies the constructed quotient `domainLift`
to this map and image proof. The lift therefore uses the actual refining
strong numerator supplied by that construction. Its triangle gives the
commuting square

```text
originalDomain A P  --incP-->  A
       |                      |
domainPreimageMap             F
       |                      |
       v                      v
originalDomain B S  --incS-->  B.
```

`domainPreimageMap_comp_inclusion` proves the square equation. The formula
`domainPreimageMap_apply` states that the value at a point `x : P` is
precisely `F(x.val)`, considered in the literal target subspace `S`.

For any pair of quotient arrows `G : C ⟶ A` and
`H : C ⟶ originalDomain B S` satisfying `G ≫ F = H ≫ incS`,
`image_mem_domainPreimage` evaluates this equality through the literal-space
functor. The subtype membership of `H(x)` then shows that `G(x)` lies in
`P`. `domainPreimageLift` is the proved domain factorization of `G` with this
image condition. Its first projection equation is the domain-lift triangle.
For the second, compose with `incS`, use the square and first projection
equations, then cancel the already proved monomorphism `incS`.

`domainPreimageCone` bundles the displayed square, and
`domainPreimageIsLimit` constructs its limiting structure. The lift is the
one just described for every commuting cone; uniqueness follows by
cancelling the monomorphism `incP`. Thus `domainPreimage_isPullback`
establishes base change of original-domain inclusions for all quotient
morphisms. No existence of a fiber product or output analytic square is
assumed.

General analytic gluing and finite-gluing saturation, the full analytic
category comparison, etale and quasi-etale morphism classes and sites,
equivariant sites, compact and distinguished domains, and the Harris tower
specialization remain obligations of the surrounding task.

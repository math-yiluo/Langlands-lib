# The glued analytification space of a scheme locally of finite type

This unit constructs the underlying topological space of the analytification of
a scheme `X` locally of finite type over a complete nonarchimedean field `K`.
It glues the Library's polynomial-locus analytifications of all affine open
subschemes along the maps induced by restriction of global sections. The unit
constructs the space, its canonical maps from the affine analytifications, its
open sets and its universal property for continuous maps. It does not prove
that the canonical maps are open embeddings, or that the space agrees with the
affine analytification when `X` is affine. Those facts are left to later
statement units.

## Provenance

Berkovich, *Spectral Theory and Analytic Geometry over Non-Archimedean Fields*
(1990), proof of Theorem 3.4.1, printed pp.63–64/PDF pp.77–78, builds `X^an` in
three steps. Step (1) treats affine space. Step (2) shows that for an open
subscheme `X ⊆ Y` the open subset `π^{-1}(X)` of `Y^an` is `X^an`, and treats
closed subschemes. Step (3) covers an arbitrary `X` by open affine subschemes
and glues their analytifications, using the universal property and step (2).
The registered source is
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
SHA256 `9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`.

Conrad, *Weil and Grothendieck approaches to adelic points* (2011), printed
p.19, final paragraph of the proof of Proposition 5.11(3), appeals to the
analytification of [CT]. Conrad describes it as compatible with fibre products,
open and closed immersions, étale maps, the scheme case and extension of the
ground field. Conrad–Temkin, *Non-archimedean analytification of
algebraic spaces* (2009), Theorem 2.2.3, printed pp.7–8, builds the
analytification of algebraic spaces from the analytifications of schemes. The
registered sources are `conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`, and
`conrad-temkin-2009-nonarchimedean-analytification`, SHA256
`ecfb9dad9c7e27ec36e3a40111ea140fc3bf2589f41b58f97e036e4e2ce6394e`.

Berkovich glues along a chosen affine covering. Here the construction uses every
affine open of `X` and every inclusion between two of them. It therefore
depends on no choice of covering, only on the chosen polynomial presentations of
the affine coordinate rings. The quotient below is the colimit, in topological
spaces, of the diagram of affine analytifications indexed by the affine opens.
These are derived implementation choices. Conrad–Temkin work with rigid-analytic
spaces; the Library space is a Berkovich-style glued spectrum.

## Hypotheses

All declarations lie in `Langlands.Analytic.SchemeAnalytification`. In the
algebraic section `K` is any commutative ring and `X` and `Y` are schemes in
universe `u`, the universe of `K`. From the section on the glued space on, `K`
is a nontrivially normed, ultrametric and complete field.
`f : X ⟶ Spec (CommRingCat.of K)` is the structure morphism. It is
`LocallyOfFiniteType`. No quasi-compactness, quasi-separatedness,
separatedness, reducedness or nonemptiness of `X` is assumed.

## Coordinate maps and restrictions

`coordinateMap g hg` is the `K`-algebra map `CoordinateRing fY →ₐ[K]
CoordinateRing fX` given by `g.appTop` on global sections. Here `g : X ⟶ Y`
is a morphism of schemes with `hg : g ≫ fY = fX`. `CoordinateRing` is the
published actual global-section algebra of `AffineSchemeAnalytification`, with
`K`-algebra structure from the structure morphism. Compatibility with these
algebra structures follows from `Scheme.Hom.comp_appTop` and `hg`.
`coordinateMap_apply` records the underlying function.

For an affine open `U : X.affineOpens`, `structureMap f U` is the composite
`U.ι ≫ f` from the open subscheme `U` to `Spec K`. Mathlib's instances make
`U` affine and `U.ι ≫ f` locally of finite type. For affine opens `V ≤ U`,
`restriction f h` is `coordinateMap` of the inclusion `X.homOfLE h : V ⟶ U`.
It is over `Spec K` by `Scheme.homOfLE_ι`. It is the restriction of global
sections from `U` to `V`.

## Local analytifications and their maps

`chartPresentation K f U` is the published chosen finite polynomial presentation
`AffineSchemeAnalytification.presentation (structureMap f U)` of the global
sections of `U`. `LocalSpace K f U` is the published polynomial-locus space
`AffineAnalytification.Space K (chartPresentation K f U)`.

For `h : V ≤ U`, `localMap K f h : C(LocalSpace K f V, LocalSpace K f U)` is
`AffineAnalytification.baseMap` of `restriction f h`. This is the continuous map
of affine analytifications induced by the restriction of global sections
(`AffineAnalytificationMap`).

## The glued space

`Glue K f` is the relation on the sigma type `Σ U : X.affineOpens, LocalSpace K
f U` that relates `⟨V, y⟩` to `⟨U, localMap K f h y⟩` for all `h : V ≤ U` and all
`y`. `Space K f` is `Quot (Glue K f)`, the quotient by the equivalence relation
generated by `Glue K f`. Its topology is the quotient topology of the sigma
topology.

`ι K f U : C(LocalSpace K f U, Space K f)` is the canonical continuous map,
composed of the sigma injection and the quotient map; `ι_apply` unfolds it.
`ι_localMap` proves `ι K f U (localMap K f h y) = ι K f V y`. `exists_ι` shows
that every point of `Space K f` lies in the image of some `ι K f U`.
`isQuotientMap_mk` records that the quotient map is a quotient map. `isOpen_iff`
characterizes the open sets: `s` is open exactly when `ι K f U ⁻¹' s` is open
for every affine open `U`.

## Universal property

For a topological space `T`, a family `g U : C(LocalSpace K f U, T)` with
`g U (localMap K f h y) = g V y` for all `h : V ≤ U` descends to
`desc K f g hg : C(Space K f, T)`. `desc_ι` proves `desc K f g hg (ι K f U y) =
g U y`. `desc_unique` proves that two continuous maps out of `Space K f` that
agree after every `ι K f U` are equal.

## Scope

The unit does not prove that `ι K f U` is injective, open or an embedding. It
does not prove that `Space K f` is Hausdorff when `X` is separated, or that
the canonical map from the analytification of the affine open `⊤` is a
homeomorphism when `X` is affine. It constructs no affinoid atlas
or analytic structure on `Space K f`, and no maps induced by morphisms of
schemes. It proves no independence of the chosen presentations, and no
comparison with rational points or with the rigid analytification of
Conrad–Temkin. These remain successor obligations of the parent task.

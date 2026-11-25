# Maps from affinoid spectra to a polynomial-locus analytification

This module takes a presented affinoid algebra `R` over `K` and a `K`-algebra map
`φ : A →ₐ[K] R`, where `A` is a presented affine `K`-algebra. It constructs the
induced map from the affinoid spectrum `M(R)` to the polynomial-locus
analytification of `Spec A`. The module builds the bounded chart map, the
continuous map of spaces, the chosen-chart atlas morphism from the singleton
atlas of `M(R)` and the strong atlas map defined for every admissible chart pair.
In the other direction, it constructs from every strong map out of the singleton
atlas a `K`-algebra map `A → R`. The module does not state that the two
constructions are mutually inverse or natural; that is the statement
`AffineAnalytificationAffinoidUniversalStatement`, proved as
`affineAnalytificationAffinoidUniversal` in
`AffineAnalytificationAffinoidUniversalProof`.

## Provenance

The analytic spaces, charts and atlases are the Library's existing
polynomial-locus construction (`AffineAnalytificationGluing` and
`AffineAnalytificationAtlas`). The singleton atlas of an affinoid spectrum is the
Library's `PresentedAffinoidSpace.atlasPresentation` (`AffinoidSpectrumAtlas`).

The source is Berkovich, *Spectral Theory and Analytic Geometry over
Non-Archimedean Fields* (1990), §3.4. Theorem 3.4.1, printed p.63/PDF p.77,
defines `X^an` for a scheme `X` locally of finite type over `k`, with `k`
nontrivially valued. It represents the functor sending a `k`-analytic space `𝒳`
to the set `Hom_k(𝒳, X)` of morphisms of `k`-ringed spaces. Step (1) of its proof,
printed p.64/PDF p.78, identifies
`Hom_k(𝒳, 𝔸^n) ≅ Γ(𝒳, 𝒪_𝒳)^n ≅ Hom_k(𝒳, Spec k[T_1, …, T_n])`. For an affinoid
space `𝒳 = M(R)`, the global functions are `R`, so `Hom_k(M(R), Spec A)` is the
set of `k`-algebra maps `A → R`. This module constructs the analytic map belonging
to such an algebra map. Remark 3.4.2, printed p.64/PDF p.78, describes
`Spec(A)^an` as the multiplicative seminorms on `A` extending the norm of `k`.
The registered source is
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
SHA256 `9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`.

Conrad, *Weil and Grothendieck approaches to adelic points* (2011), printed
p.19, in the final paragraph of the proof of Proposition 5.11(3), uses the
functorial analytification of Conrad–Temkin and its functorial property
`X(k) = X^an(k)` as sets. For `R = K`, the maps constructed here are the affine
case of the comparison between `K`-points and analytic `K`-points. The
registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

The explicit construction below is not in these sources. It is a derived
implementation for the Library's model: the radius level, the Tate evaluation
chart map, the transport to the selected chart and the atlas morphisms. It
follows the published `AffineAnalytificationMap`, whose source is the atlas of a
second presentation rather than one affinoid chart.

## Hypotheses

All declarations except one lie in `Langlands.Analytic.AffineAnalytification`.
The field `K` is nontrivially normed and ultrametric. `A` is a commutative
`K`-algebra in any universe, and `P : FinitePolynomialPresentation K A` is a
surjection `P.map` from a polynomial ring in `P.arity` variables. `R` is an
arbitrary presented affinoid algebra over `K`, in `K`'s universe, possibly
nonreduced, zero or with empty spectrum. `φ` is an arbitrary `K`-algebra map.
No norm on `A`, positive arity or nonemptiness is assumed. From the section on
the chart map on, `K` is also complete, as the chart algebras require.

## Generator values and the radius level

`affinoidValue K P R φ t` is `φ (P.map (X t))`, the image in `R` of the `t`-th
generator of `A`. `exists_affinoidValue_le` gives a radius index `l` such that
every generator value has quotient norm at most `radius K l`. It applies
`exists_radius_gt` to the sum of these norms. `affinoidLevel K P R φ` is the least
such index, chosen by `Nat.find` with classical decidability.
`norm_affinoidValue_le` records its defining property.
`affinoidValue_hasBoundedMonomials` deduces, through
`GeneralizedTateAlgebra.monomialValue_norm_le_weight`, that the weighted
monomials of the generator values for the constant polyradius at this level have
norm at most one.

## The bounded chart map

`affinoidTateMap K P R φ` is the Library's bounded evaluation homomorphism
`GeneralizedTateAlgebra.evaluateHom` from the generalized Tate algebra of
polyradius `polyradius K P.arity (affinoidLevel K P R φ)` to `R`, at the generator
values. `affinoidTateMap_X` evaluates the variables.
`affinoidTateMap_polynomialMap` shows that on the image of a polynomial `p` it
gives `φ (P.map p)`. Both sides are `K`-algebra maps of the polynomial ring that
agree on the variables.

`affinoidChartMap K P R φ : BoundedAlgHom K (algebra K P (affinoidLevel K P R φ))
R` descends `affinoidTateMap` through `PresentedAffinoidAlgebra.descendRelations`
to the actual chart algebra. That algebra is the quotient of the Tate algebra by
the closed ideal generated by `PolynomialLocus.relations`, the images of the
polynomials in the kernel of `P.map`. A kernel polynomial `p` goes to
`φ (P.map p) = φ 0 = 0`, so the relations are respected.
`affinoidChartMap_coordinate` evaluates it on the coordinates.
`affinoidChartMap_algebraMap` proves that it sends the coordinate-algebra image
`PolynomialLocus.algebraMap` of `a : A` to `φ a`. The proof lifts `a` through
`P.map`.

## The continuous map and the atlas morphisms

`affinoidBaseMap K P R φ : C(BanachSpectrum R, Space K P)` sends a point `x` to
the point `chart K P (affinoidLevel K P R φ)` of the pulled-back seminorm
`BanachSpectrum.comap (affinoidChartMap K P R φ) x`. It is continuous as the
composite of `BanachSpectrum.comapContinuous` with the continuous chart.
`affinoidBaseMap_apply` records this formula.

`affinoidIndex K P R φ` is the selected chart `representative K P (affinoidLevel K
P R φ)` of the constructed atlas. It is typed as an index of
`(presentation K P).atlas`. `affinoidPullback K P R φ` is the bounded map from
that chart algebra to `R`: the published transport
`representativeEquiv` to the radius level, followed by `affinoidChartMap`.
`affinoidPullback_algebraMap` proves that it also sends the coordinate-algebra
image of `a` to `φ a`. It uses the published `equalRangeEquiv_algebraMap`.

`affinoidAtlasHom K P R φ` is the chosen-chart morphism
`Hom (PresentedAffinoidSpace.atlasPresentation (Opposite.op R)) (presentation K P)`.
Its base map is `affinoidBaseMap`, its single selected target chart is
`affinoidIndex`, and its pullback is `affinoidPullback`. Chart commutation uses
the published `chart_comap_representativeEquiv`. The singleton atlas has only
identity restrictions, and the identity restriction of the target is the
identity by `restriction_id`, so restriction commutation is the identity law of
composition.

`affinoidStrongHom K P R φ` is the all-admissible-pair strong map
`StrongHom.ofDirected (affinoidAtlasHom K P R φ) (atlas_hasDirectedCharts K P)`.
Its pullbacks to other admissible target charts are the Library's unique
factorizations through the directed charts of `P`. `affinoidStrongHom_baseMap`
identifies its base map with `affinoidBaseMap` (definitional).

`Langlands.Analytic.PresentedAffinoidSpace.atlasPresentation_hasDirectedCharts`
proves that the singleton atlas of any presented affinoid spectrum, over any
complete ultrametric normed field, has directed charts. Its unique chart contains
every chart. This is the only declaration outside
`Langlands.Analytic.AffineAnalytification`. The statement
`AffineAnalytificationAffinoidUniversalStatement` uses it to
compose strong maps out of singleton atlases.

## The algebra map of a strong map

Let `F` be a strong map from the singleton atlas of `M(R)` to `presentation K P`.
`strongHomTarget F` is a target chart, chosen from `F.target_exists`, that contains
the image of the single chart. `strongHomTarget_spec` records this containment.
`strongHomAlgHom F : A →ₐ[K] R` is the coordinate-algebra map
`PolynomialLocus.algebraMap` of the chosen target chart, followed by the
underlying algebra map of the bounded pullback of `F` to that chart.
`strongHomAlgHom_apply` records this formula. This module does not prove that the
result is independent of the chosen target chart.

## Scope

The module does not state the following: that
`strongHomAlgHom` is independent of the target chart, that `affinoidStrongHom`
and `strongHomAlgHom` are mutually inverse, the seminorm formula for the image
points, naturality in `R` or in `A`, or the analogous bijection for morphisms in
the localized category `SaturatedAtlasPresentation.LocalizedCategory`. The
statement `AffineAnalytificationAffinoidUniversalStatement` states the
first five for strong maps. The localized-category version needs the comparison
of localized morphisms out of an affinoid with strong maps from its refinements.
It is not treated here, nor are schemes that are not affine, algebraic spaces
and extension of the ground field.

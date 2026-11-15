# Maps of polynomial-locus analytifications induced by algebra maps

This unit takes a `K`-algebra map `f : A →ₐ[K] B` between presented affine
`K`-algebras and constructs the induced map of their polynomial-locus
analytifications. The map goes the other way, `Space K Q → Space K P`, as
for the analytification of the scheme morphism `Spec B → Spec A`. The unit
constructs the bounded chart maps, the glued continuous map of spaces, the
chosen-chart morphism of the constructed affinoid atlases and the strong
atlas map defined for every admissible chart pair. Identity and composition
laws, independence of the presentations and agreement with other
analytification constructions are not stated here.

## Provenance

The analytic spaces, charts and atlases are the Library's existing
polynomial-locus construction (`AffineAnalytificationGluing` and
`AffineAnalytificationAtlas`). That construction is derived from Berkovich,
*Spectral Theory and Analytic Geometry over Non-Archimedean Fields* (1990), the
proof of Theorem 3.4.1, steps (1)–(3), printed pp.63–64/PDF pp.77–78. In
Theorem 3.4.1, printed p.63/PDF p.77, the analytification `X^an` of a scheme
of locally finite type is the representing object of a functor, so it is
functorial in `X`. Proposition 3.4.6,
printed p.65/PDF p.79, uses the corresponding morphism `g^an : Y^an → X^an` of
a scheme morphism `g : Y → X`. Remark 3.4.2, printed p.64/PDF p.78, describes
`Spec(A)^an` as the multiplicative seminorms on `A` extending the norm of the
ground field. The registered source is
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
SHA256 `9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`.

Conrad–Temkin, *Non-archimedean analytification of algebraic spaces* (2009),
Theorem 2.2.3, printed pp.7–8, constructs `f^an` for algebraic spaces from the
analytified scheme maps of étale charts. The registered source is
`conrad-temkin-2009-nonarchimedean-analytification`, SHA256
`ecfb9dad9c7e27ec36e3a40111ea140fc3bf2589f41b58f97e036e4e2ce6394e`. Conrad,
*Weil and Grothendieck approaches to adelic points* (2011), printed p.19, in
the final paragraph of the proof of Proposition 5.11(3), relies on this
"functorial theory of analytification". The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

None of these sources use the explicit constructions below. They are derived
implementation choices for the Library's polynomial-locus model: the chosen
polynomial lifts of generator images, the monotone radius levels, the Tate
evaluation chart maps, the gluing of the chart maps and the atlas morphisms.
Conrad–Temkin work with rigid-analytic spaces; the Library space is a
Berkovich-style glued spectrum.

## Hypotheses

All declarations lie in `Langlands.Analytic.AffineAnalytification`. The field
`K` is nontrivially normed and ultrametric. `A` and `B` are commutative
`K`-algebras, possibly in different universes. `P : FinitePolynomialPresentation
K A` and `Q : FinitePolynomialPresentation K B` are surjections `P.map` and
`Q.map` from polynomial rings in `P.arity` and `Q.arity` variables. The map `f`
is an arbitrary `K`-algebra map. From the section on chart maps on, `K` is also
complete, as the chart algebras require. No norm on `A` or `B`, positive arity,
nonemptiness, injectivity, surjectivity or finiteness of `f` is assumed.

## Lifts of the generator images

`generatorLift K P Q f t` is a polynomial in the variables of `Q` chosen, by
surjectivity of `Q.map`, to present `f (P.map (X t))`. `map_generatorLift`
records this choice. `map_aeval_generatorLift` proves
`Q.map (aeval (generatorLift K P Q f) p) = f (P.map p)` for every polynomial `p`
in the variables of `P`. Both sides are `K`-algebra maps of the polynomial ring,
and they agree on the variables.

`generatorValue K P Q f k t` is the image of the `t`-th lift in the `k`-th chart
algebra `algebra K Q k` of `Q`, under `PolynomialLocus.polynomialMap`.
`generatorValue_eq_algebraMap` proves that it equals the image of
`f (P.map (X t))` under the explicit coordinate-algebra map
`PolynomialLocus.algebraMap`. So these values do not depend on the chosen
lifts.

## Radius levels

`exists_generatorValue_le` gives, for each `k`, a radius index `l` such that the
quotient norm of every generator value is at most `radius K l`. It uses
`exists_radius_gt` for the sum of these norms. `minimalLevel K P Q f k` is the
least such index, chosen by `Nat.find` with classical decidability, and
`norm_generatorValue_le_minimalLevel` records its defining property.

`level K P Q f k` is the supremum of `minimalLevel` over `0, …, k`.
`minimalLevel_le_level` and `level_mono` show that it bounds `minimalLevel` and
is monotone in `k`. `norm_generatorValue_le` therefore bounds the generator
values in the `k`-th chart of `Q` by `radius K (level K P Q f k)`.
`generatorValue_hasBoundedMonomials` deduces, through
`GeneralizedTateAlgebra.monomialValue_norm_le_weight`, that the weighted
monomials of the generator values for the constant polyradius at this level
have norm at most one.

## The bounded chart maps

`tateMap K P Q f k` is the Library's bounded evaluation homomorphism
`GeneralizedTateAlgebra.evaluateHom` from the generalized Tate algebra of
polyradius `polyradius K P.arity (level K P Q f k)` to `algebra K Q k`, at the
generator values. `tateMap_X` evaluates the variables. `tateMap_polynomialMap`
shows that on polynomials it is substitution of the lifts followed by
`PolynomialLocus.polynomialMap`. `polynomialMap_aeval_generatorLift` rewrites
this as the coordinate-algebra map applied to `f (P.map p)`.

`chartMap K P Q f k : BoundedAlgHom K (algebra K P (level K P Q f k)) (algebra K Q
k)` descends `tateMap` through `PresentedAffinoidAlgebra.descendRelations` to the
actual chart algebra of `P`. That algebra is the quotient of the Tate algebra by
the closed ideal generated by `PolynomialLocus.relations`, the images of the
polynomials in the kernel of `P.map`. A kernel polynomial `p` is sent to the
coordinate-algebra image of `f (P.map p) = f 0 = 0`, so the relations are
respected. The following lemmas compute the chart map:

- `chartMap_presentationMap`: on the quotient map it is `tateMap`
  (definitional);
- `chartMap_coordinate`: on the coordinates it gives the generator values;
- `chartMap_algebraMap`: it sends the coordinate-algebra image of `a : A` to the
  coordinate-algebra image of `f a`. The proof lifts `a` through `P.map`.

`restriction_generatorValue` shows that the actual radius restrictions of `Q`
carry generator values to generator values. `restriction_comp_chartMap`
proves, for `k ≤ k'`, that restricting from chart `k'` to chart `k` of `Q` after
`chartMap` at `k'` equals `chartMap` at `k` after the restriction of `P` from
level `level K P Q f k'` to level `level K P Q f k`. Both sides are bounded maps
out of a presented affinoid algebra, so by
`PresentedAffinoidAlgebra.hom_ext_coordinate` it suffices to compare them on
coordinates.

## The continuous map of analytic spaces

`sigmaMap K P Q f` sends a pair `⟨k, x⟩` of a chart index of `Q` and a point
`x` of the Berkovich spectrum of `algebra K Q k` to the point `chart K P (level K
P Q f k)` of the pulled-back seminorm `BanachSpectrum.comap (chartMap K P Q f k)
x`. `comap_chartMap_pull` and `sigmaMap_pull` show that this is compatible with
the chart system's `pull` maps along the restrictions of `Q`. The proof uses
`restriction_comp_chartMap` and the published `chart_pull`.

`Space K Q` is the quotient of the disjoint union of the chart spectra by the
relation identifying points with a common pull from a smaller chart.
`baseFun K P Q f` is the quotient lift of `sigmaMap`, which respects the
relation by `sigmaMap_pull`. `continuous_baseFun` proves continuity. Each
component is the continuous `BanachSpectrum.comapContinuous` of the chart map,
composed with the continuous chart of `P`; `Continuous.quotient_lift` applies.
`baseMap K P Q f : C(Space K Q, Space K P)` is this continuous map.

`baseMap_chart` is the `rfl` computation on chart points.
`coordinateNorm_baseMap_chart` proves that the `t`-th coordinate norm of the
image of `chart K Q k x` is the value of `x` at the `t`-th generator value.
`baseMap_range_chart_subset` shows that the image of the `k`-th chart range of
`Q` lies in the chart range of `P` at `level K P Q f k`.

## Transport to the selected charts

The atlas `(presentation K P).atlas` of `AffineAnalytificationAtlas` uses the
selected least representative `representative K P m` of each chart range, and
`representativeEquiv K P m` is the published bounded equivalence from the
selected chart algebra to `algebra K P m`.

`chart_comap_representativeEquiv` proves that pulling a spectrum point back
along this equivalence and applying the selected chart gives the same point as
the original chart. The proof compares both points over the chart at the
maximum of the two indices, using `equalRangeEquiv_comp_restriction` and
`chart_pull`. `representativeEquiv_coordinate` proves that the equivalence
sends coordinates to coordinates, by the same comparison with
`PolynomialLocus.restriction_coordinate`.

## The chosen-chart and strong atlas morphisms

`indexMap K P Q f i` assigns to a selected chart `i` of `Q` the selected
representative of the chart of `P` at `level K P Q f i.val`.
`range_chart_indexMap` identifies its range with that original chart range.
`indexMap_mono` proves that inclusions of selected chart ranges of `Q` give
inclusions of the assigned ranges of `P`. It uses the published
`selected_range_subset_iff`, `level_mono` and `range_chart_mono`.

`pullback K P Q f i` is `chartMap` at `i.val` composed with
`representativeEquiv` at `level K P Q f i.val`. `pullback_coordinate` computes
it on coordinates. `pullback_algebraMap` proves that it sends the
coordinate-algebra image of `a : A` to that of `f a`, using the published
`equalRangeEquiv_algebraMap` and `chartMap_algebraMap`.
`chart_comm_atlasHom` proves the chart commutation required for an atlas
morphism, from `chart_comap_representativeEquiv`. `restriction_comp_pullback`
proves the restriction compatibility on coordinates, as for
`restriction_comp_chartMap`.

`atlasHom K P Q f : AffinoidAtlasPresentation.Hom (presentation K Q)
(presentation K P)` is the morphism of constructed atlases with base map
`baseMap K P Q f`, chart assignment `indexMap K P Q f` and bounded pullbacks
`pullback K P Q f`. This is the Library's chosen-chart morphism structure of
`ChosenAtlasMorphisms`. Its restriction law is obtained from
`restriction_comp_pullback` after `selected_range_subset_iff` converts range
inclusions into inequalities of the original indices.

`strongHom K P Q f : StrongHom (presentation K Q) (presentation K P)` is the
published `StrongHom.ofDirected` of `atlasHom` and the directedness
`atlas_hasDirectedCharts` of the target atlas. It provides an actual bounded
pullback for every pair of a source chart and an admissible target chart
containing its image, with chart commutation and restriction naturality for all
such pairs. `strongHom_baseMap` is the `rfl` lemma identifying its base map
with `baseMap K P Q f`.

## Scope

This unit gives definitions and their computation lemmas. It does not state or
prove the following:

- that the construction sends identity maps and composites to identity and
  composite morphisms;
- that it does not depend on the chosen presentations up to the Library's
  atlas equivalences;
- compatibility with the rational-point maps of
  `AffineAnalytificationRationalPoints`;
- functoriality for morphisms of nonaffine schemes or algebraic spaces, or
  compatibility with extension of the ground field;
- comparison with other analytification constructions in the Library.

These are planned as separate statement units with proof successors.

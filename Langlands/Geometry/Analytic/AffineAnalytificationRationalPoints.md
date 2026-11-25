# Rational points of the polynomial-locus analytification

This module constructs the maps between the algebraic `K`-points of a presented
affine `K`-algebra `A` and the points of its polynomial-locus analytification
`AffineAnalytification.Space K P`. An algebraic point `φ : A →ₐ[K] K` goes to an
actual point of the glued Berkovich space and to an actual `K`-valued point of
the constructed affinoid atlas. A `K`-valued point of that atlas goes back to an
algebraic point, and the round trip from algebraic points is the identity. The
other round trip, bijectivity, the topological comparison and the saturated-atlas
version are stated in `AffineAnalytificationRationalPointsStatement`.

## Provenance

The analytic space, its charts and its atlas are the Library's existing
polynomial-locus construction (`AffineAnalytificationGluing` and
`AffineAnalytificationAtlas`). That construction is derived from Berkovich,
*Spectral Theory and Analytic Geometry over Non-Archimedean Fields* (1990), the
proof of Theorem 3.4.1, steps (1)–(3), printed p.64/PDF p.78. The registered
source is
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
SHA256 `9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`.

The comparison prepared here is the affine case of the identification of the
rational points of an algebraic space with the rational points of its
analytification. Conrad–Temkin, *Non-archimedean analytification of algebraic
spaces* (2009), Example 2.3.2, printed pp.11–12, shows that this map is a
bijection that preserves residue fields. The registered source is
`conrad-temkin-2009-nonarchimedean-analytification`, SHA256
`ecfb9dad9c7e27ec36e3a40111ea140fc3bf2589f41b58f97e036e4e2ce6394e`. Conrad,
*Weil and Grothendieck approaches to adelic points* (2011), printed p.19,
uses this identification, `X(k) = X^an(k)` as sets, to retopologize `X(k)` by
admissible affinoid coverings in the proof of Proposition 5.11(3). The registered
source is `conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

Neither source uses the explicit constructions below. They are derived
implementation choices for the Library's polynomial-locus model: the
minimal-radius chart, the Tate evaluation characters, the chart-wise field
point and the chart-independent inverse. Conrad–Temkin work with rigid-analytic
spaces, while the Library space is a Berkovich-style glued spectrum. The rational
points used here are therefore the Library's `FieldPoint` structures: points
together with compatible `K`-valued characters of all chart algebras that
contain them. They are not maximal points of a rigid space.

## Hypotheses

All declarations lie in `Langlands.Analytic.AffineAnalytification`. The field
`K` is nontrivially normed. The input `P : FinitePolynomialPresentation K A` is a
surjection `P.map` from a polynomial ring in `P.arity` variables onto the
commutative `K`-algebra `A`. Algebraic points are the Library's
`PointTopology.AlgPoint K A K`, a named copy of `A →ₐ[K] K`. The radius
declarations need nothing more. From the section on evaluation characters on,
`K` is also ultrametric and complete, as the chart algebras require. No norm on
`A`, positive arity, nonemptiness, reducedness or finiteness of the point set is
assumed.

## Minimal radius of an algebraic point

`pointCoordinates K P φ i = φ (P.map (X i))` are the coordinates of `φ` in the
presentation variables. `RadiusAdmits K P φ m` states that every coordinate has
norm at most `radius K m = ‖ϖ‖⁻ᵐ`, the radius of the `m`-th closed polydisc of
the construction. `RadiusAdmits.mono` uses monotonicity of the radii. Some index
always admits the point (`exists_radiusAdmits`): `exists_radius_gt` gives a
radius larger than the sum of the coordinate norms, and each norm is at most
this sum. `minimalRadius K P φ` is the least admitting index, chosen by
`Nat.find` with classical decidability. `radiusAdmits_minimalRadius` and
`minimalRadius_le` record its two defining properties.

`hasBoundedMonomials` proves that, for an admitting index, the weighted
monomials of the coordinates are bounded by one. Each monomial's norm is a
product of powers of coordinate norms, each at most the corresponding power of
the radius. The proof uses `Finset.prod_le_prod₀` and `pow_le_pow_left₀`.

## Evaluation characters of the bounded charts

`tateEvaluation K P hm` is the Library's bounded evaluation homomorphism
`GeneralizedTateAlgebra.evaluateHom` from the generalized Tate algebra of the
`m`-th constant polyradius to `K`, at the coordinates of `φ`. `tateEvaluation_X`
evaluates the variables. `tateEvaluation_polynomialMap` shows that on
polynomials this evaluation is `φ ∘ P.map`. Both are `K`-algebra maps on the
polynomial ring, and the proof checks that they agree on the variables.

`character K P hm : BoundedAlgHom K (algebra K P m) K` descends this evaluation
through `PresentedAffinoidAlgebra.descendRelations` to the actual chart algebra.
That algebra is the quotient by the closed ideal generated by
`PolynomialLocus.relations P (polyradius K P.arity m)`, the images of the
polynomials in the kernel of `P.map`. The relations are respected because such a
polynomial `p` satisfies `P.map p = 0`, so its evaluation is `φ 0 = 0`. The
following lemmas compute the character:

- `character_presentationMap`: on the quotient map, it is the Tate evaluation
  (definitional);
- `character_coordinate`: on the coordinates, it gives `pointCoordinates`;
- `character_algebraMap`: on the explicit coordinate-algebra map
  `PolynomialLocus.algebraMap` from `A`, it is `φ` itself. The proof lifts the
  element of `A` through the surjection `P.map`.

`character_comp_restriction` proves that the characters commute with the
actual radius restrictions `restriction K P h : algebra K P k → algebra K P m`
for `m ≤ k`. The two bounded maps agree after the presentation map of the
larger chart. This follows from `GeneralizedTateAlgebra.hom_ext` on coordinates
and `PolynomialLocus.restriction_coordinate`. Then
`PresentedAffinoidAlgebra.hom_ext_presentation` removes the presentation map.

## The analytic point

`spectrumPoint K P hm` is the multiplicative seminorm `a ↦ ‖character K P hm a‖`
on the `m`-th chart algebra. It is defined as
`BanachSpectrum.comap` of the character, applied to the canonical point
`BanachSpectrum.fieldPoint K`, and `spectrumPoint_apply` computes it.
`pull_spectrumPoint` shows that the chart system's `pull` maps for the actual
restrictions carry these spectrum points to each other.

`analyticPoint K P φ : Space K P` is the image of the spectrum point at the
minimal admitting radius under the `chart K P` map of the glued space.
`chart_spectrumPoint` proves that every admitting index gives the same point. It
uses `chart_pull` from the minimal index together with `pull_spectrumPoint`.
`coordinateNorm_analyticPoint` computes the coordinate norms of this point as
the norms of the algebraic coordinates. `analyticPoint_mem_range_chart_iff`
then shows, through the published `mem_range_chart_iff`, that `analyticPoint K P
φ` lies in the range of the `m`-th chart exactly when `m` admits `φ`.

## Field-valued points of the constructed atlas

The atlas `(presentation K P).atlas` of `AffineAnalytificationAtlas` has
selected indices `i`. Each has an original natural index `i.val`, the chart
algebra `algebra K P i.val` and the chart map `chart K P i.val`.

`toFieldPoint K P φ : FieldPoint K (presentation K P)` has as its point
`analyticPoint K P φ`. On each selected chart whose range contains this point,
its evaluation is `character K P` at the admitting index supplied by
`analyticPoint_mem_range_chart_iff`, regarded as a `K`-algebra map. The
`isChartPoint` field is witnessed by the spectrum point of the same chart,
through `chart_spectrumPoint`; the norm identity holds by definition. The
restriction law combines `character_comp_restriction` with the published
`selected_range_subset_iff`, which turns a range inclusion between selected
charts into the inequality of their original indices that selects the
restriction. `toFieldPoint_point` is the `rfl` simp lemma for the point.

`chartAlgebraMap K P i` is the explicit map `PolynomialLocus.algebraMap` from
`A` to the algebra of the selected chart `i`. `chosenChart K P p` chooses a
selected chart containing the point of a field-valued point `p`. Such a chart
exists by `IndexedAffinoidAtlas.exists_mem_range_chart`, and
`mem_range_chosenChart` records membership. `toAlgPoint K P p` is the algebraic
point given by the evaluation of `p` on this chart, composed with
`chartAlgebraMap`.

`toAlgPoint_apply_eq` proves that the choice of chart does not matter: every
selected chart containing the point computes the same value on every `a : A`.
Given two such charts with original indices `i.val` and `j.val`, the proof uses
the selected representative of the original chart at `min i.val j.val`. Its range
is that original range, it lies in both given ranges, and it contains the point.
The field-valued point's restriction law, together with
`PolynomialLocus.restriction_algebraMap`, compares the evaluations on each
larger chart with the evaluation on this smaller one.

`toAlgPoint_toFieldPoint` proves `toAlgPoint K P (toFieldPoint K P φ) = φ`. On
the chosen chart, the evaluation is the character, and `character_algebraMap`
identifies its composite with the coordinate-algebra map with `φ`.

## Scope

This module gives definitions and their computation lemmas. It does not state or
prove the following:

- that `toFieldPoint` is bijective;
- that `analyticPoint` is a topological embedding for the evaluation topology on
  algebraic points;
- the analogous equivalence with the `K`-valued points of the saturated atlas
  `saturated K P`.

These comparisons are stated in `AffineAnalytificationRationalPointsStatement`
and proved in `AffineAnalytificationRationalPointsProof`. This module also does not cover independence of the presentation,
functoriality in affine scheme morphisms, the gluing to nonaffine schemes and
algebraic spaces, or extension of the ground field.

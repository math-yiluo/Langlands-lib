# Proof: strong maps from affinoid spectra to an affine analytification

`Langlands.Analytic.AffineAnalytification.affineAnalytificationAffinoidUniversal`
has exactly the type
`AffineAnalytificationAffinoidUniversalStatement.{u, v, w}`, with independent
universes for `K`, `A` and `B` and no additional premises. It proves all six
assertions of the published statement. Its only import is
`AffineAnalytificationAffinoidUniversalStatement`; the statement and its
dependencies are unchanged. The auxiliary lemmas are proved in this file, in
the namespace `AffinoidUniversalComparison`.

## Source, provenance and scope

The mathematical source of the target is Berkovich, *Spectral Theory and
Analytic Geometry over Non-Archimedean Fields* (1990), Theorem 3.4.1 and its
proof, printed pp.63–64/PDF pp.77–78, and Remark 3.4.2, printed p.64/PDF p.78.
The registered source is
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
SHA256 `9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`,
retained as `literature/Berkovich 1990 Spectral theory and analytic geometry over non-Archimedean fields.pdf`.
Section 3.4 assumes a nontrivial valuation. The theorem represents the functor
of morphisms of `K`-ringed spaces into a scheme locally of finite type.
Steps (1)–(3) construct this representative for affine schemes from affine
space and closed subschemes. Testing it on `M(R)`, whose global functions are
`R`, gives the algebra-map correspondence. Remark 3.4.2 gives the description
of points by multiplicative seminorms extending the field norm.

The target is the Library's derived formulation for the constructed
polynomial-locus atlas. This proof establishes that formulation directly from
the existing constructions of charts, restrictions, bounded pullbacks and
strong atlas maps. Its coordinate-comparison arguments follow those of the proof
of the identity, composition and presentation-independence laws for affine
analytification strong maps (`AffineAnalytificationFunctorialityProof`). The
needed comparisons are proved here; `AffineAnalytificationFunctorialityProof` is
not imported.

The hypotheses are precisely those of the target: `K` is complete,
ultrametric and nontrivially normed; `A` and `B` are commutative `K`-algebras
with finite polynomial presentations; `R` and `R'` are arbitrary presented
affinoid algebras. No reducedness, nonempty spectrum or positive arity is
required. The result concerns strong maps from the singleton affinoid atlas.
It does not establish the universal property in the localized category or
for arbitrary analytic test spaces.

## Coordinate comparison

`coordinate_eq_algebraMap` identifies each chart coordinate with the image of
`P.map (X t)` under `PolynomialLocus.algebraMap`.
`atlas_restriction_coordinate` uses the published restriction formula to show
that restrictions preserve coordinates. `exists_common_chart` is the
published directedness of the constructed atlas.

For `pullback_coordinate_eq`, put two admissible target charts in a common
chart. Strong-map compatibility with restriction expresses the pullback from
that common chart through either original chart. Because restrictions
preserve coordinates, both original coordinate values equal the value from
the common chart.

For `strongHom_eq_of_coordinate`, move the two selected pullbacks for each
source chart to a common target chart. The coordinate comparison and
`PresentedAffinoidAlgebra.hom_ext_coordinate` give equality of these bounded
algebra maps. Chart compatibility and the supplied cover of the source then
give equality of the base maps. Finally, `StrongHom.ext_of_directed` gives
equality of the full strong maps, including every admissible pullback.
Thus the argument uses equality of algebra maps and also applies to
nonreduced algebras.

## Algebra maps and the single chart

`algHom_ext_generators` proves that two `K`-algebra maps out of `A` are equal if
they agree on the generators `P.map (X t)`. Their composites with the surjection
`P.map` agree by `MvPolynomial.algHom_ext`. `singleton_cover` states that the
single chart of an affinoid spectrum covers it, since the chart is the identity.

## Assertion (1)

`pullback_coordinate_indep` specializes `pullback_coordinate_eq` to the single
source chart. In `pullback_algebraMap_eq`, the `K`-algebra map
`a ↦ F.pullback PUnit.unit j h (PolynomialLocus.algebraMap P _ a)` agrees with
`strongHomAlgHom F` on every generator. After rewriting coordinates by
`coordinate_eq_algebraMap`, this is `pullback_coordinate_indep` for `j` and the
chosen target chart `strongHomTarget F`. `algHom_ext_generators` concludes.

## Assertions (2)–(4)

`affinoidStrongHom_pullback_selected` identifies the pullback of
`affinoidStrongHom K P R φ` at the selected chart `affinoidIndex K P R φ` with
`affinoidPullback K P R φ`, by the Library's `StrongHom.ofDirected_pullback_selected`.
`affinoidStrongHom_pullback_coordinate` evaluates it on coordinates with the
published `affinoidPullback_algebraMap`: the `t`-th coordinate goes to
`φ (P.map (X t))`.

For (2), `strongHomAlgHom_affinoidStrongHom` applies assertion (1) at the selected
chart and then `affinoidPullback_algebraMap`. For (3),
`affinoidStrongHom_strongHomAlgHom` applies `strongHom_eq_of_coordinate`. It
compares the selected pullback of `affinoidStrongHom K P R (strongHomAlgHom F)`
with the pullback of `F` at `strongHomTarget F`. On the `t`-th coordinate both
give `strongHomAlgHom F (P.map (X t))`, the second by `coordinate_eq_algebraMap`
and `strongHomAlgHom_apply`. For (4), `pointSeminorm_affinoidStrongHom` unfolds
the base map to a chart point, applies the published `pointSeminorm_chart` and
`chartSeminorm_apply`, and finishes with `affinoidChartMap_algebraMap`.

## Assertions (5) and (6)

Both composites are compared with the right-hand side by
`strongHom_eq_of_coordinate`. The right-hand side uses its selected chart and
`affinoidStrongHom_pullback_coordinate`. For the composite, the Library's
`StrongHom.compOfDirected_pullback` expresses its pullback at an admissible
chain as the composite of the two given pullbacks. The admissibility of the
composite chain is proved directly from the two image inclusions.

In `compOfDirected_strongAtlasMap` (5), the chain is the single chart of `M(R)`
followed by the selected chart of `affinoidStrongHom K P R φ`. The first
pullback is the original bounded map `g`, by the Library's
`PresentedAffinoidSpace.strongAtlasMap_pullback`. On the `t`-th coordinate the
composite gives `g (φ (P.map (X t)))`, which is the right-hand side.

In `compOfDirected_strongHom` (6), the chain is the selected chart
`affinoidIndex K Q R ψ` followed by the chart `indexMap K P Q f` of the published
chosen-chart morphism `atlasHom K P Q f`. Both pullbacks are the selected ones,
by `StrongHom.ofDirected_pullback_selected`. The published `pullback_algebraMap`
sends the `t`-th coordinate to the image of `f (P.map (X t))`, and
`affinoidPullback_algebraMap` then gives `ψ (f (P.map (X t)))`.

## Main theorem

`affineAnalytificationAffinoidUniversal` introduces the field, instances,
algebra and presentation, then assembles the six assertions in the order of
the unchanged target. It uses the standard axioms `propext`, `Classical.choice`
and `Quot.sound`.

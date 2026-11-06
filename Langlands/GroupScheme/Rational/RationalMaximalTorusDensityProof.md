# Density of conjugators onto ground-field maximal tori

Worker 1574, with Worker 1337 contributing to the parameter-scheme proof route and
its geometric density input.

`Langlands.GroupScheme.rationalMaximalTorusConjugateDensity` proves exactly the
unchanged Library proposition
`Langlands.GroupScheme.RationalMaximalTorusConjugateDensityStatement.{u}` from
`Rational/RationalMaximalTorusDensityStatement`, at arbitrary universe `u`.
It applies to every infinite field `k : Type u`, every smooth affine group
scheme `G` over `Spec k` with connected underlying space, and every maximal
`k`-torus `j₀ : T₀.toGrp ⟶ G`. Its conclusion is density in the underlying
space of `G_K`, where `K = AlgebraicClosure k`, of the union of the images of
those actual `K`-points `g` for which an actual closed `k`-torus `j : T ⟶ G`
satisfies
`range ((j₀)_K ≫ (G_K.innerIso g).hom) = range (j_K)`.
This is equality of subgroup functors on all scheme tests.

## Imported inputs and the final Lean term

The proof is one application of
`rationalMaximalTorusConjugateDensity_of_parameter_statements` from
`Rational/RationalMaximalTorusDensityComposition` to the published theorems
`maximalTorusParameterExistence` from
`Rational/MaximalTorusParameterExistenceProof` and
`maximalTorusParameterUnirational` from
`Rational/MaximalTorusParameterUnirationalProof`.
The first proves `MaximalTorusParameterExistenceStatement.{u}`; the second
proves `MaximalTorusParameterUnirationalStatement.{u}`. Both premises of the
composition theorem are supplied by these proofs. No parameter proposition,
field restriction, or other theorem-valued premise remains in the final type.
The target statement and its imported files are unchanged.

## Parameter construction and its compatibility

The existence theorem supplies an actual `Q` and `q : G.X ⟶ Q` with
`IsMaximalTorusParameter j₀ q`. Its construction represents the smooth closed
torus normalizer using `torusNormalizerSmoothClosed`, then applies
`smoothSubgroupQuotientExistence` to obtain the smooth quotient map. Smoothness
of `Q` follows by descent along this map. Equal parameter images are precisely
right-normalizer cosets on every scheme test.

For each ground-field section `x` of `Q`,
`MaximalTorusParameterExistence.conjugationCompatible_of_fiber` supplies one
actual closed ground-field torus. If a geometric lift of `x` exists, the
conjugate of `(T₀)_K` descends by fpqc closed-subgroup descent: the normalizer
fiber relation gives the required overlap equality. The same fiber relation
shows that every lift of `x` gives that same subgroup functor. Thus the torus
is chosen for `x` before quantifying over its lifts. This is the full
`TorusParameterConjugationCompatible` property consumed by the density
reduction; a universal torus over `Q` is unnecessary for this predicate.

## Unirationality of the same parameter scheme

The unirationality theorem applies to the particular `Q` and `q` supplied by
existence. It yields `IsUnirational k Q`: an actual morphism over `k` from a
nonempty open subscheme of finite-dimensional affine space into this `Q`,
with dense underlying image.

The imported proof constructs a generic torus conjugator by the published
isogeny reduction, semisimple-centralizer construction, maximal-torus
conjugacy and base-change results, and induction on Lie dimension. The
all-test normalizer fiber relation for `q` descends the generic conjugator's
composite with `q` along an fpqc covering, giving a dense point of `Q` over a
finite rational function field. `HasDenseRationalFunctionFieldPoint.isUnirational`
then spreads it to the required affine-open morphism. These are imported
proved constructions into the original `Q`, as explained in the
unirationality proof's paired Markdown.

## The implemented density deduction

The imported composition theorem performs the following steps.

1. `IsUnirational.hasDenseRationalPoints`, from
   `AlgebraicGeometry/PointTopology/UnirationalDensity`, gives dense
   ground-field sections of `Q`. This is where `Infinite k` is used.
2. `hasDenseGeometricRationalPoints_of_hasDenseRationalPoints`, from
   `AlgebraicGeometry/PointTopology/GeometricRationalDensityExtension`, proves
   density of their actual scalar extensions in `Q_K`. Its proof identifies
   each extended section's image with the inverse image of its original
   image under the open scalar-extension projection.
3. Smoothness of `q` survives base change, so the actual map `q_K` is open and
   locally of finite type. `dense_torusConjugators_of_parameters`, from
   `Rational/RationalMaximalTorusDensityReduction`, applies to this map, the
   geometric density, and the conjugation compatibility supplied above.
   In its lifting lemma, the image of any nonempty open of `G_K` meets a
   chosen parameter. The locally finite type rational-point lifting result
   over the algebraically closed field `K` provides a lift inside that open.
   Compatibility makes every such lift a conjugator counted in the target.
   Density passes to the full target union.

This final module is an internal composition of the named Library proofs.
Its proof explanation follows the implemented route. It adds no external
source assertion and no perfectness, reductivity, splitness or characteristic
hypothesis.

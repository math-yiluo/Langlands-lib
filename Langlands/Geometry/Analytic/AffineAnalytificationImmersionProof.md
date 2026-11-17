# Proof: analytification of affine closed and basic open immersions

The theorem
`Langlands.Analytic.AffineAnalytification.affineAnalytificationImmersion`
proves the unchanged
`AffineAnalytificationImmersionStatement.{u, v, w, x}` in four independent
universes.

For a complete, ultrametric, nontrivially normed field `K` and a finite
polynomial presentation `P` of a commutative `K`-algebra `A`, it proves:

1. A surjective `K`-algebra map `f : A →ₐ[K] B` induces a closed embedding
   `baseMap K P Q f`, for every finite polynomial presentation `Q` of `B`.
2. For every `g : A`, every localization `B` of `A` away from `g` with
   compatible `K`-algebra structure, and every finite polynomial presentation
   `Q` of `B`, the map induced by `A → B` is an open embedding.
3. If in addition `C` is an `A`-algebra with compatible `K`-algebra structure,
   its structure map is surjective with kernel `Ideal.span {g}`, and `R`
   presents `C`, then the ranges of the maps for `A → B` and `A → C` are
   complementary subsets of `Space K P`.

The compatibility in the second and third clauses is
`IsScalarTower K A B` and `IsScalarTower K A C`, respectively. The algebras
may have nilpotents or be zero rings, and `g` is arbitrary.

## Dependencies and proof through seminorms

The module imports the unchanged target statement,
`AffineAnalytificationSeminormProof`, `AnalytificationCenter`, and Mathlib's
ideal-span, valuation-quotient and valuation-localization modules.

The imported seminorm comparison supplies an embedding
`x ↦ (a ↦ pointSeminorm K P x a)` into `A → ℝ`, with the product topology,
and says that every multiplicative seminorm extending the norm of `K`
occurs. Thus points are determined by their evaluations, and continuity into
an analytification can be checked through those evaluations. The theorem
`pointSeminorm_baseMap` in `AnalytificationCenter` identifies the seminorm of
an image point with restriction along the algebra map.

All auxiliary results of the present proof are in
`Langlands.Analytic.AffineAnalytification.ImmersionComparison`.

### Valuations, quotients and localizations

An extending seminorm satisfies the ultrametric inequality by the imported
`SeminormComparison.add_le_max`. The definition `valuationOfSeminorm`
therefore regards it as a valuation with values in `ℝ≥0`.
Conversely, `seminormOfValuation` takes the underlying real values of
such a valuation; the ultrametric inequality implies the ordinary triangle
inequality needed for a multiplicative ring seminorm.

For a surjective `f : A →ₐ[K] B`, vanishing on its kernel places
`RingHom.ker f` inside the support of `valuationOfSeminorm ν hν`.
The definition `quotientSeminorm` descends this valuation using
`Valuation.onQuot` and transports it to `B` along
`RingHom.quotientKerEquivOfSurjective`. The lemmas
`quotientSeminorm_apply_map` and `quotientSeminorm_extendsNorm` prove that
the resulting seminorm restricts to `ν` and still extends the norm of `K`.

For localization away from `g`, the lemma `awayDenominators` proves that
`ν(g) ≠ 0` puts every power of `g` outside the valuation's support.
The definition `awaySeminorm` uses Mathlib's
`Valuation.extendToLocalization` and converts the extended valuation back
to a seminorm. Its restriction formula is `awaySeminorm_apply_map`, and
`awaySeminorm_extendsNorm` uses the scalar tower to check the norm on `K`.
These constructions do not assume that the localization map is injective.

### Closed embeddings

For a surjective `f : A →ₐ[K] B`, the lemma
`range_baseMap_surjective` identifies the range with

`{x | ∀ a, f a = 0 → pointSeminorm K P x a = 0}`.

The forward implication is restriction of seminorms. For the converse,
`quotientSeminorm` extends the point's seminorm to `B`. This seminorm
extends the norm of `K`, so the seminorm comparison realizes it as a point
of `Space K Q`. Injectivity of point seminorms proves that its image is
the original point.

Precomposition by `f`, from `B → ℝ` to `A → ℝ`, is a topological embedding
by `Function.Surjective.isEmbedding_comp`.
The seminorm embeddings and `pointSeminorm_baseMap` then show that
`baseMap K P Q f` is an embedding. The displayed range is closed, since it
is an intersection of zero sets of continuous evaluations. This proves
`isClosedEmbedding_baseMap_surjective`.

The lemma `range_baseMap_quotient_singleton` specializes the range when
`RingHom.ker f = Ideal.span {g}`: it is exactly
`{z | pointSeminorm K P z g = 0}`. One direction uses membership of `g`
in the ideal. For the other, `Ideal.span_singleton_le_iff_mem` shows that
the entire ideal lies in the point seminorm's kernel.

### Basic open embeddings

For an Away localization at `g`, the lemma `range_baseMap_away` identifies
the range with

`U = {x | pointSeminorm K P x g ≠ 0}`.

Necessity is `seminorm_map_generator_ne_zero`, obtained by applying a
seminorm to the equation expressing the inverse of the image of `g`.
For the converse, `pointOfSeminorm` chooses the point represented by an
extending seminorm, and `awaySection` applies this to `awaySeminorm`.
The restriction formula and injectivity of point seminorms prove
`baseMap_awaySection`, which gives the required preimage.

For every seminorm on `B`, `seminorm_fraction` proves
`ν(b) = ν(algebraMap A B a) / ν(algebraMap A B g)^n`, where
`(a, n) = IsLocalization.Away.sec g b`. The equation follows by applying
the seminorm to `IsLocalization.Away.sec_spec` and dividing by the
nonzero value of the denominator. It also proves `seminorm_away_ext`:
a seminorm on `B` is determined by its restriction to `A`.

The set `U` is open by continuity of evaluation at `g`. For the above
fixed representation of `b`, the function

`z ↦ pointSeminorm K P z a / pointSeminorm K P z g ^ n`

is continuous on `U`, since its denominator never vanishes there.
These evaluation formulas prove `continuous_awaySection` by the
seminorm embedding and continuity into a product. Corestrict the original
map to `U`. The map `awaySection` is a continuous left inverse to this
corestriction, using `seminorm_away_ext` and point-seminorm injectivity.
The continuous-left-inverse criterion proves that the corestriction,
and hence the original map, is an embedding. Its range is `U`, proving
`isOpenEmbedding_baseMap_away`.

### Complementary ranges

The lemmas `range_baseMap_away` and
`range_baseMap_quotient_singleton` identify the two ranges with
`{z | pointSeminorm K P z g ≠ 0}` and
`{z | pointSeminorm K P z g = 0}`. These sets are complementary by
definition, proving `range_baseMap_away_compl`.
The main theorem combines the three clauses.

## Sources and scope

Berkovich, *Spectral theory and analytic geometry over non-Archimedean
fields* (1990), registered as
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
SHA-256
`9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`:

- Proposition 3.4.7(2), printed p.66/PDF p.80, gives preservation and
  reflection of closed immersions.
- Proposition 3.4.6(8), printed p.65/PDF p.79, with its proof on printed
  p.66/PDF p.80, gives preservation and reflection of open immersions.
- The forward implications refer to step (2) of the proof of Theorem
  3.4.1, printed p.64/PDF p.78, which realizes open and closed subschemes
  as the corresponding analytic subspaces.
- The proof of Proposition 3.4.4, printed p.65/PDF p.79, gives the identity
  between the analytification of a reduced closed complement and the
  complement of the inverse image of an open subset.
- Remark 3.4.2, printed p.64/PDF p.78, identifies the set of points of
  affine analytification with multiplicative seminorms extending the
  ground-field norm.

The Lean proof uses this seminorm description, together with the topology
established by the seminorm comparison. Its quotient and localization
arguments differ from the analytic-subspace construction in the book.
The principal-ideal calculation proves the complement assertion directly,
so the quotient need not be reduced.

Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), registered as
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`,
printed/PDF p.19, final paragraph of the proof of Proposition 5.11(3),
uses compatibility with open and closed immersions for rigid-analytic
analytification of separated algebraic spaces locally of finite type.
That use motivates this affine underlying-topological result.

The theorem proves the underlying topological forward implications for
affine closed immersions and principal open immersions, with arbitrary
finite polynomial presentations. It does not assert either converse or
an immersion statement about the analytic structure.

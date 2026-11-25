# Proof: functoriality of the polynomial-locus affine analytification

Lean module: `Langlands.Geometry.Analytic.AffineAnalytificationFunctorialityProof`.

Main theorem: `Langlands.Analytic.AffineAnalytification.affineAnalytificationFunctoriality`,
of type `AffineAnalytificationFunctorialityStatement.{u, v, w, x}`.

The target statement is
`Langlands.Analytic.AffineAnalytification.AffineAnalytificationFunctorialityStatement`
(module `Langlands.Geometry.Analytic.AffineAnalytificationFunctorialityStatement`).
Let `K` be a complete, ultrametric, nontrivially normed field. Let `P` and `P'` be
finite polynomial presentations of a commutative `K`-algebra `A`, `Q` one of `B` and
`R` one of `C`, and let `f : A →ₐ[K] B` and `g : B →ₐ[K] C`. The statement asserts:

1. `strongHom K P P (AlgHom.id K A) = StrongHom.id (presentation K P)`;
2. `strongHom K P R (g.comp f)` equals
   `StrongHom.compOfDirected (strongHom K Q R g) (strongHom K P Q f)
   (atlas_hasDirectedCharts K Q) (atlas_hasDirectedCharts K P)`;
3. `StrongHom.compOfDirected (strongHom K P' P (AlgHom.id K A))
   (strongHom K P P' (AlgHom.id K A)) (atlas_hasDirectedCharts K P')
   (atlas_hasDirectedCharts K P) = StrongHom.id (presentation K P)`.

## Provenance

The coordinate argument was checked against the published target, and the target,
the imported APIs and the cited originals were compared. The auxiliary lemmas are derived internally
from the published chart and strong-map constructions.

## Imports and dependency

The module imports only the statement module, and through it the published modules
`Langlands.Geometry.Analytic.AffineAnalytificationMap` and
`Langlands.Geometry.Analytic.DirectedAtlasComposition`. It does not use the seminorm
comparison (`AffineAnalytificationSeminormProof`).

The proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`. All
auxiliary declarations live in the namespace
`Langlands.Analytic.AffineAnalytification.FunctorialityComparison`. They are internal
steps of this proof.

## Implemented route

The proof never compares points through seminorms. It shows that a strong map into the
constructed atlas of `P` is determined by the values of its pullbacks on the
coordinates. It then computes these values for each side of the three equalities.

### Step 1: coordinates of the constructed atlas

- `coordinate_eq_algebraMap`: the `t`-th coordinate of the chart algebra
  `algebra K P m` is the coordinate-algebra image
  `PolynomialLocus.algebraMap P (polyradius K P.arity m) (P.map (X t))` of the `t`-th
  generator of `A`. It follows from `PolynomialLocus.algebraMap_map` and
  `PolynomialLocus.polynomialMap_X`.
- `atlas_restriction_coordinate`: the atlas restrictions of `presentation K P` send
  coordinates to coordinates (`PolynomialLocus.restriction_coordinate`).
- `exists_mem_range_chart`: every point of the analytification lies in the range of a
  selected chart. A point is `chart K P m s` for some `m` (`exists_chart`), and the
  selected chart `representative K P m` has the same range (`range_representative`).
- `exists_common_chart`: two selected charts lie in a common selected chart. This is
  `atlas_hasDirectedCharts K P`, restated with the index type of
  `(presentation K P).atlas`.

### Step 2: strong maps into the constructed atlas

Let `X : AffinoidAtlasPresentation.{u, u, 0} K`, the universe profile of each
constructed affine presentation, and let `F, G : StrongHom X (presentation K P)`.
The main theorem retains four independent universes: `K : Type u`, `A : Type v`,
`B : Type w` and `C : Type x`; this auxiliary universe profile imposes no equality
between those four parameters.

- `pullback_coordinate_eq`: for a source chart `i` and two admissible target charts
  `j` and `j'`, the pullbacks `F.pullback i j` and `F.pullback i j'` take the same
  value on the `t`-th coordinates. Choose a common chart `q` of `j` and `j'`. By
  `StrongHom.pullback_comp_restriction`, `F.pullback i q` is `F.pullback i j` composed
  with the restriction from `q` to `j`, and that restriction sends the `t`-th
  coordinate to the `t`-th coordinate. The same holds for `j'`.
- `strongHom_eq_of_coordinate`: assume that the source charts cover `X`, and that for
  each source chart `i` there are admissible target charts `j` for `F` and `j'` for
  `G` whose pullbacks agree on all coordinates. Then `F = G`.
  - Pass to a common chart `q` of `j` and `j'`. By `pullback_coordinate_eq` the
    pullbacks `F.pullback i q` and `G.pullback i q` agree on the coordinates. So they
    are equal by `PresentedAffinoidAlgebra.hom_ext_coordinate`.
  - The base maps agree: a point of `X` is `X.atlas.chart i y` for some `i` and `y`.
    By `StrongHom.chart_comm`, `F` and `G` send it to the image under the chart `q`
    of the comaps of `y` along the equal pullbacks `F.pullback i q` and
    `G.pullback i q`.
  - `StrongHom.ext_of_directed`, with the directed charts of `P`, then gives `F = G`
    from the equal base maps and one equal admissible pullback for each source chart.

### Step 3: pullbacks of the induced strong maps

- `strongHom_pullback_coordinate`: for every admissible pair `(i, j)`, the pullback
  `(strongHom K P Q f).pullback i j` sends the `t`-th coordinate to
  `PolynomialLocus.algebraMap Q (polyradius K Q.arity i.val) (f (P.map (X t)))`. By
  `pullback_coordinate_eq` one may use the selected target chart
  `(atlasHom K P Q f).indexMap i` instead of `j`. There the pullback is
  `(atlasHom K P Q f).pullback i` (`StrongHom.ofDirected_pullback_selected`, since
  `strongHom` is `StrongHom.ofDirected (atlasHom K P Q f)`). Its value on the
  coordinate is given by the published `pullback_coordinate` and
  `generatorValue_eq_algebraMap`.
- `strongHom_pullback_algebraMap`: for every admissible pair `(i, j)` and `a : A`,
  `(strongHom K P Q f).pullback i j` sends
  `PolynomialLocus.algebraMap P (polyradius K P.arity j.val) a` to
  `PolynomialLocus.algebraMap Q (polyradius K Q.arity i.val) (f a)`. Both sides,
  precomposed with `P.map`, are `K`-algebra maps out of the polynomial ring. They
  agree on the variables by `coordinate_eq_algebraMap` and
  `strongHom_pullback_coordinate`, so they are equal
  (`MvPolynomial.algHom_ext`). Then use the surjectivity of `P.map`.

### Step 4: the three clauses

Each clause is an instance of `strongHom_eq_of_coordinate`, with the cover given by
`exists_mem_range_chart`.

- `strongHom_id` (clause 1): for a chart `i` of `P`, use the selected target chart of
  `atlasHom K P P (AlgHom.id K A)` on the left, and `i` itself on the right. The left
  pullback sends the `t`-th coordinate to
  `PolynomialLocus.algebraMap P (polyradius K P.arity i.val) (P.map (X t))`
  (`strongHom_pullback_coordinate`). By `coordinate_eq_algebraMap`, this is the `t`-th
  coordinate of chart `i`. The right pullback is the restriction from `i` to `i`,
  which fixes the coordinate (`atlas_restriction_coordinate`).
- `strongHom_comp` (clause 2): for a chart `i` of `R`, choose an admissible target `j`
  of `strongHom K Q R g` and an admissible target `k` of `strongHom K P Q f` on `j`.
  Then `k` is admissible for the composite (`StrongHom.comp_admissible`), and the
  composite pullback is `(strongHom K Q R g).pullback i j` after
  `(strongHom K P Q f).pullback j k` (`StrongHom.compOfDirected_pullback`). On the
  `t`-th coordinate, `strongHom_pullback_coordinate` for `f` and
  `strongHom_pullback_algebraMap` for `g` give the value
  `PolynomialLocus.algebraMap R (polyradius K R.arity i.val) (g (f (P.map (X t))))`.
  `strongHom_pullback_coordinate` for `g.comp f` gives the same value on the left.
- `strongHom_id_comp_id` (clause 3): the same computation with `Q = P'`, `R = P` and
  both maps the identity of `A` gives the value
  `PolynomialLocus.algebraMap P (polyradius K P.arity i.val) (P.map (X t))`. As in
  clause 1, this is the `t`-th coordinate of chart `i`, which is also the value of
  the identity pullback.

The main theorem `affineAnalytificationFunctoriality` combines the three clauses.
Exchanging the arbitrary presentations `P` and `P'` in clause 3 gives the reverse
composite identity as well.

## Sources

The statement is the affine content, in the Library's explicit polynomial-locus model,
of the functoriality of analytification. In Berkovich 1990, *Spectral theory and
analytic geometry over non-Archimedean fields* (registered
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`),
Theorem 3.4.1 (printed p.63/PDF p.77) defines `X^an` as a representing object, and
functoriality follows from the Yoneda lemma. In Conrad–Temkin 2009, *Non-archimedean
analytification of algebraic spaces* (registered
`conrad-temkin-2009-nonarchimedean-analytification`), Theorem 2.2.3 and its proof
(printed pp.7–8) give functoriality and independence of choices for algebraic spaces.
Brian Conrad uses the functorial theory of analytification in *Weil and Grothendieck
approaches to adelic points* (December 31, 2011; registered
`conrad-2011-weil-grothendieck-adelic-points`), printed p.19, final paragraph of the
proof of Proposition 5.11(3).

The Lean route differs from the cited constructions. Berkovich uses a representing
property, while Conrad–Temkin prove independence and functoriality using common étale
refinements and equivalent lifts. The proof here works directly with the explicit
model: a strong map into the constructed atlas is determined by the coordinate values of its pullbacks, and these values are
computed from the published formulas for the chosen-chart pullbacks.

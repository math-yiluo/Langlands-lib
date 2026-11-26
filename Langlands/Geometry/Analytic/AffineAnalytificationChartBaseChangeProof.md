# Fixed-radius comparison of affine charts under ground field extension

The theorem
`Langlands.Analytic.AffineAnalytification.affineAnalytificationChartBaseChange`
proves
`Langlands.Analytic.AffineAnalytification.AffineAnalytificationChartBaseChangeStatement.{u, u', v}`.
The fields `K` and `L` are complete, ultrametric and nontrivially normed, with
`NormedAlgebra K L`. The commutative `K`-algebra `A` has a finite polynomial
presentation `P`, and `r` is any positive polyradius on its generators.
The universes of `K`, `L` and `A` are independent.

## Evaluation on a chart

Over an ultrametric normed field `F`, let `g : A →ₐ[F] E` take values in a
complete ultrametric normed commutative `F`-algebra `E`. Suppose the images
`g (P.map (MvPolynomial.X i))` satisfy `HasBoundedMonomials` at `r`. The lemma
`eval_poly` compares weighted Tate-algebra evaluation with `g.comp P.map`
on polynomials. The two algebra maps agree on the variables by `evaluate_X`,
so `MvPolynomial.algHom_ext` gives agreement on every polynomial. In
particular, a polynomial in the kernel of `P.map` evaluates to zero.
`evaluateRelations` then descends evaluation through the closed relation
ideal and gives the bounded algebra map `liftChart` on
`PolynomialLocus.chart P r`. The surjectivity of `P.map` and
`PolynomialLocus.algebraMap_map` give `liftChart (algebraMap a) = g a`
for every `a : A`.

## The two maps

Write `Q` for `baseChangePresentation K L P`, `B` for the `K`-chart at
`r`, `BL` for `GroundFieldExtension.algebra K L B`, and `C` for the chart
of `Q` at `r`. The proof also regards `C` as a normed `K`-algebra by
restriction of scalars.

The forward map starts with `q : A →ₐ[K] C`, obtained by applying the chart
map of `Q` to `1 ⊗ a`. By `baseChangePresentation_map_X`, `q` sends the
generators of `P` to the coordinates of `C`. By `norm_coordinate_le` and
`monomialValue_norm_le_weight`, each monomial in those values has norm
at most its weight at `r`. Thus `liftChart` gives a bounded `K`-algebra map
`B → C`, and `GroundFieldExtension.lift` extends it to a bounded `L`-algebra
map `f : BL → C`.

For the reverse map, the original chart map followed by `iota` is a
`K`-algebra map `A → BL`. `Algebra.TensorProduct.liftEquivRight` extends it to
an `L`-algebra map from `L ⊗[K] A` to `BL`. Its values on the generators of `Q`
are the coordinates of `BL` by `baseChangePresentation_map_X` and
`iota_coordinate`. The same monomial estimate gives a bounded
`L`-algebra map `g : C → BL` by `liftChart`.

By `lift_iota` and `liftChart_algebraMap`, `f` sends
`iota (PolynomialLocus.algebraMap P r a)` to
`q a = PolynomialLocus.algebraMap Q r (1 ⊗ a)` for every `a : A`.
On generators this gives the coordinate formula for `f`, and
`liftChart_algebraMap` gives the reverse coordinate formula for `g`.
Both composites fix their presentation coordinates, so `hom_ext_coordinate`
identifies them with the identities. `BoundedAlgEquiv.ofHomInv` gives the
required equivalence with `f` as its forward map.

## Mathematical context

The chart comparison is an input to the scheme-level compatibility of
analytification with ground field extension. Conrad–Temkin's *Non-archimedean
analytification of algebraic spaces* identifies the scheme comparison as the
usual isomorphism in Theorem 2.3.5, printed and PDF p. 13
(`conrad-temkin-2009-nonarchimedean-analytification`, SHA-256
`ecfb9dad9c7e27ec36e3a40111ea140fc3bf2589f41b58f97e036e4e2ce6394e`).
Conrad uses the ground field compatibility in the final paragraph of the
proof of Proposition 5.11(3) of *Weil and Grothendieck approaches to adelic
points*, p. 19 (`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`).

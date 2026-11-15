# The multiplicative seminorm of a point of the affine analytification

This unit gives each point of the Library's polynomial-locus affine
analytification `Space K P` a multiplicative seminorm on the presented algebra
`A`. It proves that this seminorm extends the norm of `K` and that each
evaluation `x ↦ |a|_x` is continuous on `Space K P`. Injectivity, the image
(every multiplicative seminorm extending the norm of `K`) and the agreement of
topologies are not claimed here. They are left to a later statement unit.

## Provenance

Berkovich, *Spectral Theory and Analytic Geometry over Non-Archimedean Fields*
(1990), Remark 3.4.2, printed p.64/PDF p.78: if `X = Spec(A)` for a finitely
generated `k`-algebra `A`, then `X^an` is the set of all multiplicative
seminorms on `A` whose restriction to `k` is the norm of `k`. Definition
1.5.1, printed p.19/PDF p.33, gives affine space this seminorm description and
the weakest topology that makes every function `x ↦ |f(x)|` continuous. The
registered source is
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
SHA256 `9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`.
The space `Space K P` is the Library's existing construction
(`AffineAnalytificationGluing`), derived from the proof of Berkovich's
Theorem 3.4.1, steps (1)–(3), printed pp.63–64/PDF pp.77–78. Each bounded
polynomial locus there is the spectrum of an affinoid algebra, and a spectrum
point is a bounded multiplicative seminorm (Berkovich §1.2, printed
pp.12–13/PDF pp.26–27).

Conrad, *Weil and Grothendieck approaches to adelic points* (2011), printed
p.15, in the remark after the statement of Proposition 5.4, says that his
original proof went through Berkovich spaces by way of [CT]. On printed p.19,
in the final paragraph of the proof of Proposition 5.11(3), he uses the
functorial analytification. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

The source makes the seminorm description of a point a remark about the
analytic space. The chart-by-chart construction below, together with its
compatibility with the radius restrictions and the gluing, is a derived
implementation for the Library's model.

## Hypotheses

All declarations lie in `Langlands.Analytic.AffineAnalytification`. `K` is a
nontrivially normed field with an ultrametric distance. `A` is a commutative
`K`-algebra with a finite polynomial presentation
`P : FinitePolynomialPresentation K A`. The definitions `ExtendsNorm` and
`chartSeminorm` use only these hypotheses. From `chartSeminorm_pull` onwards,
`K` is also complete, as the published `Space K P` requires.

## Declarations

- `ExtendsNorm K ν` says that a multiplicative seminorm
  `ν : MulRingSeminorm A` satisfies `ν (algebraMap K A c) = ‖c‖` for every
  `c : K`. This is the condition "whose restriction to `k` is the norm on `k`"
  in Remark 3.4.2.
- `chartSeminorm K P m s` is the multiplicative seminorm
  `a ↦ s (PolynomialLocus.algebraMap P (polyradius K P.arity m) a)` on `A`,
  for a point `s` of the spectrum of the `m`-th bounded chart algebra
  `algebra K P m`. Here `PolynomialLocus.algebraMap` is the published
  `K`-algebra map from `A` to the chart quotient. The seminorm axioms come from
  those of `s` and the ring-map laws. `chartSeminorm_apply` is the defining
  equation.
- `chartSeminorm_pull`: if `m ≤ k`, pulling `s` back along the published
  radius restriction to the `k`-th chart does not change its seminorm on `A`.
  The proof uses `PolynomialLocus.restriction_algebraMap`.
- `chartSeminorm_glued`: two chart points identified by the gluing relation
  `(chartSystem K P).Glued` have the same seminorm on `A`. Both are pullbacks
  of one point of a common smaller chart.
- `pointSeminorm K P : Space K P → MulRingSeminorm A` is the descent of
  `chartSeminorm` to the glued quotient. `pointSeminorm_chart` gives its value
  at `chart K P m s`.
- `continuous_pointSeminorm_apply`: for each `a : A`, the function
  `x ↦ pointSeminorm K P x a` is continuous on `Space K P`. On each chart it
  is the continuous evaluation of the spectrum at the image of `a`, and the
  quotient topology is the topology induced by the charts.
- `pointSeminorm_extendsNorm`: every `pointSeminorm K P x` satisfies
  `ExtendsNorm K`. A spectrum point takes the value `‖c‖` on the image of the
  scalar `c` (the published `BanachSpectrum.algebraMap_apply`), and the chart
  map is a `K`-algebra map.

## Scope

The unit imports the published `AffineAnalytificationGluing` and
`Spectrum.Properties` unchanged and edits no published input. It does not state
that `pointSeminorm` is injective, that every multiplicative seminorm extending
the norm of `K` comes from a point, or that the topology of `Space K P` is the
weakest one making all evaluations continuous. These claims make up the full
content of Remark 3.4.2 and Definition 1.5.1 for this model.

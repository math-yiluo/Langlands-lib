# Statement: naturality of the analytic points of algebraic rational points

`AffineAnalytificationRationalPointNaturalityStatement` states that the analytic
point attached to an algebraic `K`-point is natural in `K`-algebra maps. Take the
Library's polynomial-locus affine analytification and the map between
analytifications induced by an algebra map `f : A → B`. Applying this map to the
analytic point of a `K`-point `φ` of `B` gives the analytic point of the
`K`-point `φ ∘ f` of `A`. This is a statement only; its proof is a separate
successor.

## Source

Conrad–Temkin, *Non-archimedean analytification of algebraic spaces* (2009),
Example 2.3.2, printed pp.11–12, identifies the closed points of `X` with the
points of `X^an`, preserving residue fields, so that `X(K) = X^an(K)`. The
identification sends a closed point `j : Spec(k') → X` to the point given by
its analytification `j^an`. Theorem 2.2.3, printed pp.7–8, makes `X ↦ X^an` a
functor, with maps `f^an` of analytifications. Functoriality, in the form
`(f ∘ j)^an = f^an ∘ j^an`, makes the identification of points compatible with
these maps. The source does not state this compatibility separately. The
registered source is `conrad-temkin-2009-nonarchimedean-analytification`, SHA256
`ecfb9dad9c7e27ec36e3a40111ea140fc3bf2589f41b58f97e036e4e2ce6394e`.

Conrad, *Weil and Grothendieck approaches to adelic points* (2011), printed
p.19, final paragraph of the proof of Proposition 5.11(3), uses the identification
`X(k) = X^an(k)` together with the functorial theory of analytification of [CT].
The registered source is `conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

Berkovich 1990, Proposition 3.4.6, printed p.65/PDF p.79, uses the morphism
`g^an` of analytifications attached to a morphism `g` of schemes. The Library's
space is derived from the proof of Theorem 3.4.1, steps (1)–(3), printed p.64/PDF
p.78. The registered source is
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
SHA256 `9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`.

No numbered source statement is literally this equation. It is the affine case
of the compatibility of the identification of rational points with
analytification maps, formulated for the Library's constructions. This
formulation is derived.

## Hypotheses

The field `K` is nontrivially normed, ultrametric and complete. `A` and `B` are
any commutative `K`-algebras, in independent universes.
`P : FinitePolynomialPresentation K A` and
`Q : FinitePolynomialPresentation K B` are arbitrary finite polynomial
presentations, including zero variables and the zero algebra. `f : A →ₐ[K] B`
is any `K`-algebra map, and `φ : AlgPoint K B K` is any algebraic `K`-point
of `B`.

## The equation

The statement is

`baseMap K P Q f (analyticPoint K Q φ) = analyticPoint K P (AlgPoint.precomp f φ)`.

- `analyticPoint` is defined in `AffineAnalytificationRationalPoints`. It sends an
  algebraic `K`-point to the point of the glued space `Space` given by the
  evaluation character on the chart of the least admissible radius.
- `baseMap K P Q f : C(Space K Q, Space K P)` is defined in
  `AffineAnalytificationMap`. On each chart it pulls back points along the chart
  map `algebra K P (level k) → algebra K Q k` induced by `f`.
- `AlgPoint.precomp f φ` is the composite `φ ∘ f`, from
  `Langlands.AlgebraicGeometry.PointTopology`.

The equation is between points of `Space K P`. It does not assert anything about
`FieldPoint` structures or about the atlas morphisms `atlasHom` and `strongHom`.

## Scope

The statement does not assert that `baseMap` is independent of the chosen
presentations or the chosen generator lifts. It does not assert identity or
composition laws, nor any statement for nonaffine schemes or algebraic spaces.
It also does not compare the induced map on rational points with any topology.

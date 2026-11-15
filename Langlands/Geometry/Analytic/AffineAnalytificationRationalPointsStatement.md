# Statement: rational points of the polynomial-locus analytification

`AffineAnalytificationRationalPointsStatement` states that, for the Library's
polynomial-locus analytification of a presented affine `K`-algebra, the
algebraic `K`-points and the `K`-rational analytic points agree as sets. It also
states that the algebraic points, with their evaluation topology, embed
topologically into the analytic space. This is a statement only; its proof is a
separate successor.

## Source

Conrad–Temkin, *Non-archimedean analytification of algebraic spaces* (2009),
Example 2.3.2, printed pp.11–12, shows that analytification defines a bijection
from the closed points of an analytifiable algebraic space `X` onto the ordinary
points of `X^an`, preserving residue fields. Taking residue field `K` gives
`X(K) = X^an(K)`. The registered source is
`conrad-temkin-2009-nonarchimedean-analytification`, SHA256
`ecfb9dad9c7e27ec36e3a40111ea140fc3bf2589f41b58f97e036e4e2ce6394e`.

Conrad, *Weil and Grothendieck approaches to adelic points* (2011), printed
p.19, final paragraph of the proof of Proposition 5.11(3), uses this
identification "`X(k) = X^an(k)` as sets" to topologize `X(k)` through an
admissible affinoid covering of `X^an`. Conrad states that this recovers the
topology of Proposition 5.4. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

The present statement is the affine case of both assertions, formulated for
the Library's Berkovich-style polynomial-locus space. That space is derived from
Berkovich 1990, proof of Theorem 3.4.1, steps (1)–(3), printed p.64/PDF p.78
(`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`).
Conrad–Temkin work with rigid-analytic spaces, whose points are the classical
points. In the Library's space, the `K`-rational points are the `FieldPoint`
structures: points together with compatible `K`-valued characters of the chart
algebras containing them. In clause (2), the source's topology on `X^an(k)` is
replaced by the subspace topology of the whole Berkovich space, and the
topology on `X(k)` is the Library's evaluation topology. These formulation
choices are derived.

## Hypotheses

The field `K` is nontrivially normed, ultrametric and complete. `A` is any
commutative `K`-algebra in any universe. `P : FinitePolynomialPresentation K A`
is any finite polynomial presentation, including zero variables, the zero
algebra and nonreduced algebras. No separatedness, nonemptiness or positive-arity
hypothesis is imposed.

## The three clauses

The declarations used are from `AffineAnalytificationRationalPoints`.

1. `Function.Bijective (toFieldPoint K P)`. Every `K`-valued point of the
   constructed atlas `presentation K P` comes from exactly one algebraic point
   `φ : AlgPoint K A K`. The published left-inverse identity gives injectivity.
   The content of the clause is surjectivity: every compatible family of
   `K`-valued chart characters is the family of evaluation characters of an
   algebraic point.
2. `IsEmbedding (analyticPoint K P)`. Give `AlgPoint K A K` the Library's
   evaluation topology, induced from `A → K`, and give `Space K P` its glued
   topology. Then `φ ↦ analyticPoint K P φ` is injective, continuous and
   inducing. The clause does not claim that the image is closed or open.
3. There is an equivalence
   `e : AlgPoint K A K ≃ FieldPoint K (saturated K P).presentation` with
   `(e φ).point = analyticPoint K P φ` for every `φ`. The saturated atlas
   `saturated K P` contains all local full affinoid domains, and its space is
   literally `Space K P`. The clause states that the `K`-valued points of the
   saturated presentation are also exactly the algebraic points, over the same
   analytic points. Since `analyticPoint` is injective by clause 2, every
   saturated `K`-valued point is determined by its underlying point, and these
   points are exactly the image of `analyticPoint`.

## Scope

The statement concerns affine algebras with a chosen presentation. It does not
assert independence of the presentation, functoriality in algebra maps, the
analogous statement for nonaffine schemes or algebraic spaces, or `L`-valued
points for complete extensions `L` of `K`. It does not identify the image of
`analyticPoint` with a closed subset. It also does not compare the evaluation
topology with the topology of Conrad's Proposition 5.4 for nonaffine spaces.

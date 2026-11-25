# Statement: Berkovich's center map is surjective and restricts to charts and rational points

This module states, without proof, the basic properties of Berkovich's center map
`π : X^an → X` for the Library's polynomial-locus analytification. The map is
defined in `AnalytificationCenter`. The module covers the affine center map
`AffineAnalytification.center K P` with values in the prime spectrum, and the
scheme-level map `SchemeAnalytification.center K f` with values in `X`. The
proposition is
`Langlands.Analytic.SchemeAnalytification.AnalytificationCenterStatement`.

## Provenance

Berkovich, *Spectral Theory and Analytic Geometry over Non-Archimedean Fields*
(1990), §3.4 ("GAGA: the case of nontrivial valuation"), printed
pp.63–64/PDF pp.77–78. Theorem 3.4.1 says that for a scheme `X` locally of finite
type over `k` the analytification `X^an` comes with a morphism `π : X^an → X`.
Part (i) says that for every non-Archimedean field `K` over `k` there is a
bijection `X^an(K) → X(K)`, and that `π` is surjective and induces a bijection
`X^an_0 → X_0` on closed points. Step (2) of the proof says that for an open
subscheme `X ⊆ Y` with canonical morphism `π : Y^an → Y`, the open subset
`π^{-1}(X)` of `Y^an` is `X^an`. Step (3) glues the analytifications of affine
opens. Remark 3.4.2 says that for `X = Spec(A)`, with `A` finitely generated
over `k`, the space `X^an` is the set of multiplicative seminorms on `A` whose
restriction to `k` is the norm of `k`. Section 3.4 assumes a nontrivial
valuation, as `NontriviallyNormedField` does here. The registered source is
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
SHA256 `9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`.

Conrad–Temkin, *Non-archimedean analytification of algebraic spaces* (2009),
§4.1, printed p.20/PDF p.20, uses "the fact that the natural map `W^an → W` is
surjective" for an algebraic `k`-scheme `W`. The registered source is
`conrad-temkin-2009-nonarchimedean-analytification`, SHA256
`ecfb9dad9c7e27ec36e3a40111ea140fc3bf2589f41b58f97e036e4e2ce6394e`.

Conrad, *Weil and Grothendieck approaches to adelic points* (2011), printed
p.19, final paragraph of the proof of Proposition 5.11(3), works with the
analytification `X^an` of [CT] and with `X(k)` inside it. The registered source
is `conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

How the items correspond to the sources:

- Items (1) and (4) are the surjectivity of `π` in Theorem 3.4.1(i), for affine
  and for general `X`.
- Item (5) is step (2) of the proof of Theorem 3.4.1, for an affine open of `X`
  and the glued space of the Library.
- Items (2), (3), (6) and (7) are derived. They are the case `K = k` of the
  bijection `X^an(K) → X(K)` of Theorem 3.4.1(i), together with the closed-point
  bijection, in the seminorm description of Remark 3.4.2. A `k`-point `φ` of
  `Spec(A)` gives the seminorm `a ↦ |φ(a)|`, whose kernel is `ker φ`. A
  multiplicative seminorm extending the norm of `k` whose kernel is `ker φ`
  factors through `A / ker φ = k`, so it equals that seminorm. Items (3) and (7)
  therefore say that the fibre of `π` over a `k`-rational point is a single
  point. No numbered source statement asserts these items in this form.

## Hypotheses

`K : Type u` is a nontrivially normed field that is ultrametric
(`IsUltrametricDist K`) and complete. In the affine part, `A : Type v` is a
commutative `K`-algebra with a finite polynomial presentation
`P : FinitePolynomialPresentation K A`, in an independent universe. In the scheme
part, `X : Scheme.{u}` is a scheme in the universe of `K`, and
`f : X ⟶ Spec (CommRingCat.of K)` is its structure morphism, assumed
`LocallyOfFiniteType`. No separatedness, quasi-compactness, reducedness or
nonemptiness of `X` is assumed.

## Statement

The proposition is the conjunction of an affine part and a scheme part.

Affine part, for all such `K`, `A` and `P`:

1. `AffineAnalytification.center K P : Space K P → PrimeSpectrum A` is
   surjective.
2. For every `K`-algebra map `φ : AlgPoint K A K` and every `a : A`, `a` lies in
   the prime ideal `center K P (analyticPoint K P φ)` if and only if `φ a = 0`.
   Here `analyticPoint K P φ` is the published point of `Space K P` defined by
   `φ`. So that center is the kernel of `φ`.
3. For every such `φ` and every point `x : Space K P`, if `center K P x` equals
   `center K P (analyticPoint K P φ)`, then `x = analyticPoint K P φ`.

Scheme part, for all such `K`, `X` and `f`:

4. The center map `center K f : Space K f → X` on the published glued space is
   surjective.
5. For every affine open `U`, the preimage of `U` under `center K f` equals the
   range of the canonical map `ι K f U` from the analytification of `U`.
6. For every `K`-point `p : RingPoint K (Over.mk f) K` of `X`, the center of the
   published point `analyticRationalPoint K f p` is
   `p.left (IsLocalRing.closedPoint K)`. This is the image in `X` of the unique
   point of `Spec K` under the scheme morphism `p.left : Spec K ⟶ X`.
7. For every such `p` and every `z : Space K f`, if `center K f z` equals
   `center K f (analyticRationalPoint K f p)`, then
   `z = analyticRationalPoint K f p`.

## Scope

The module supplies no proof; the statement is proved as `analytificationCenter`
in `AnalytificationCenterProof`. It imports
`AnalytificationCenter` and `SchemeAnalytificationRationalPoints`. It does not
describe the fibres of `π` over points that are not `K`-rational, the points
with finite completed residue field over `K`, or the `L`-points for extensions
`L` of `K`. It states nothing about structure sheaves, flatness of the local
maps (Theorem 3.4.1(ii)), or maps induced by morphisms of schemes. These lie
outside this statement.

# Statement: functoriality of the polynomial-locus affine analytification

`AffineAnalytificationFunctorialityStatement` states that the strong atlas maps
of `AffineAnalytificationMap` respect identities and composites, and that the
maps induced by the identity between two presentations of the same algebra are
mutually inverse. It is a `Prop`-valued definition; this module supplies no proof.

## Provenance

Berkovich, *Spectral Theory and Analytic Geometry over Non-Archimedean Fields*
(1990), Theorem 3.4.1, printed p.63/PDF p.77, defines the analytification
`X^an` of a scheme `X` of locally finite type as the representing object of the
functor `Hom(-, X)` on analytic spaces. By the Yoneda lemma, a standard
consequence that Berkovich does not spell out, a representing object is unique
up to unique isomorphism and functorial in `X`. So `X ↦ X^an` respects
identities and composites and does not depend on choices. Proposition 3.4.6, printed
p.65/PDF p.79, uses the resulting morphism `g^an`. The registered source is
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
SHA256 `9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`.

Conrad–Temkin, *Non-archimedean analytification of algebraic spaces* (2009),
Theorem 2.2.3 and its proof, printed pp.7–8, extend this to algebraic spaces:
`f^an` does not depend on the étale charts or on the lift of `f`, and the
construction is compatible with composition, so analytification is a functor.
The registered source is `conrad-temkin-2009-nonarchimedean-analytification`,
SHA256 `ecfb9dad9c7e27ec36e3a40111ea140fc3bf2589f41b58f97e036e4e2ce6394e`.
Conrad, *Weil and Grothendieck approaches to adelic points* (2011), printed
p.19, in the final paragraph of the proof of Proposition 5.11(3), relies on this
"functorial theory of analytification". The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

The sources prove functoriality through universal properties. The statement
here is a derived formulation for the Library's explicit polynomial-locus model.
It asserts equalities of the Library's `StrongHom` structures, which carry the
continuous base map together with an actual bounded pullback for every
admissible chart pair. The identity is the published `StrongHom.id`, which uses
the atlas restrictions. The composite is the published
`StrongHom.compOfDirected`, which builds every admissible pullback through
directed intermediate and final charts. Choice independence for presentations
is expressed by conjunct 3. The three conjuncts are the affine content of the
source functoriality in this model; the model and the formulation are derived.

## Hypotheses

The field `K` is nontrivially normed, ultrametric and complete. `A`, `B` and
`C` are commutative `K`-algebras in arbitrary universes. `P` and `P'` are finite
polynomial presentations of `A`, `Q` of `B` and `R` of `C`. The maps
`f : A →ₐ[K] B` and `g : B →ₐ[K] C` are arbitrary `K`-algebra maps. No
injectivity, surjectivity, finiteness, reducedness or nonemptiness is assumed.

`strongHom K P Q f : StrongHom (presentation K Q) (presentation K P)` is the map
induced by `f` from the atlas of `Q` to the atlas of `P`, as for the
analytification of `Spec B → Spec A`. The directedness proofs
`atlas_hasDirectedCharts K Q` and `atlas_hasDirectedCharts K P` of the
intermediate and final atlases are the inputs required by `compOfDirected`.

## The statement

For all such data, the following three equalities hold.

1. `strongHom K P P (AlgHom.id K A) = StrongHom.id (presentation K P)`.
2. `strongHom K P R (g.comp f)` equals
   `StrongHom.compOfDirected (strongHom K Q R g) (strongHom K P Q f)
   (atlas_hasDirectedCharts K Q) (atlas_hasDirectedCharts K P)`. This is the
   composite map from the atlas of `R` through the atlas of `Q` to the atlas of
   `P`.
3. `StrongHom.compOfDirected (strongHom K P' P (AlgHom.id K A))
   (strongHom K P P' (AlgHom.id K A)) (atlas_hasDirectedCharts K P')
   (atlas_hasDirectedCharts K P) = StrongHom.id (presentation K P)`. This is
   the map from the atlas of `P` to that of `P'` followed by the map back.
   Since `P` and `P'` are arbitrary, the reverse composite is the same
   statement with the roles exchanged.

Each equality includes equality of the continuous base maps and of every
bounded pullback.

## Truth sketch

This is not a Lean proof. A point of a chart spectrum of a presentation is
determined by its values on the image of `A`, since the polynomial images are
dense in the chart algebra and the seminorm is bounded. Two chart points with
the same restriction to `A` agree after pulling both to a common larger chart.
Hence the base maps agree. A bounded map out of a presented affinoid algebra is
determined by the coordinates. Every pullback in these equalities sends the
`t`-th coordinate of `P` to the coordinate-algebra image of the corresponding
image of `P.map (X t)`, by `generatorValue_eq_algebraMap`, `pullback_algebraMap`
and the uniqueness of pullbacks through directed charts.

## Scope

The statement does not cover compatibility with the rational-point maps of
`AffineAnalytificationRationalPoints`, nonaffine schemes, algebraic spaces,
fibre products, open or closed immersions, or extension of the ground field.

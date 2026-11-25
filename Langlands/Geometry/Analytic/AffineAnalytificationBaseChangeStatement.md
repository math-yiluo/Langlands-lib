# Statement: the ground-field base-change map of affine analytifications

This module states, without proof, two properties of the canonical continuous map
`baseChangeMap K L P : (X_L)^an → X^an`. Here `X = Spec A` for a presented
`K`-algebra `A`, `K → L` is an extension of complete non-Archimedean fields, and
`X_L = Spec (L ⊗[K] A)`. The map is defined in the published
`AffineAnalytificationScalarExtension` module. The statement says that the map is
surjective, and that over the analytic point of a `K`-rational point of `X` its
fibre is the single analytic point of the corresponding `L`-rational point of
`X_L`. The proposition is
`Langlands.Analytic.AffineAnalytification.AffineAnalytificationBaseChangeStatement`.

## Provenance

Conrad, *Weil and Grothendieck approaches to adelic points* (2011), printed
p.19, final paragraph of the proof of Proposition 5.11(3), uses the
analytification `X^an` of [CT]. It is described as "compatible with … extension of
the ground field", and "since the formation of `X^an` respects extension of the
ground field", Conrad identifies `X(k) → X(k')` with
`X^an(k) → (X^an)_{k'}(k')`. Item (2) is the part of this identification that
concerns the map `(X_L)^an → X^an`: a `K`-rational point of `X^an` has exactly one
preimage, and it is the `L`-rational point given by `X(K) → X(L)`. The registered
source is `conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

Berkovich, *Spectral Theory and Analytic Geometry over Non-Archimedean Fields*
(1990), proof of Proposition 2.2.4, printed p.29/PDF p.43, writes
`π : X ⊗̂ K → X` for "the canonical surjective map" of a `k`-affinoid space
`X = M(𝒜)` and a non-Archimedean field `K` over `k`. It also uses that
`M(𝒜_V ⊗̂ K) → M(𝒜_V)` is surjective for an affinoid domain `V`. §2.3, printed
pp.32–33/PDF pp.46–47, introduces this ground-field extension functor
`X ↦ X ⊗̂ K`. Remark 3.4.2, printed p.64/PDF p.78, says that for `X = Spec(A)`
the space `X^an` is the set of multiplicative seminorms on `A` that restrict to
the norm of `k`. The registered source is
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
SHA256 `9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`.

Conrad–Temkin, *Non-archimedean analytification of algebraic spaces* (2009),
Theorem 2.3.5, printed p.13/PDF p.13, gives a natural isomorphism
`k′ ⊗̂_k X^an ≃ (k′ ⊗_k X)^an`, "the usual isomorphism when `X` is an algebraic
`k`-scheme". That section works with rigid-analytic spaces, so this module cites
it only as context for the compatibility. The registered source is
`conrad-temkin-2009-nonarchimedean-analytification`, SHA256
`ecfb9dad9c7e27ec36e3a40111ea140fc3bf2589f41b58f97e036e4e2ce6394e`.

Both items are derived for the Library's polynomial-locus model. No numbered
source statement asserts them in this form.

- Item (1) is derived from the surjectivity of `M(𝒜 ⊗̂ L) → M(𝒜)` for the
  affinoid chart algebras `𝒜` of `P`, which Berkovich uses as known on p.29.
  Read through Remark 3.4.2, a point of `X^an` is a multiplicative seminorm on
  `A` extending the norm of `K`. A preimage is a multiplicative seminorm on
  `L ⊗[K] A` that extends the norm of `L` and restricts to the given seminorm
  along `a ↦ 1 ⊗ a`.
- Item (2) is derived from the seminorm description. A seminorm `y` in the fibre
  over the point of `φ` kills `1 ⊗ (a − φ a)` for every `a`. These elements
  generate the kernel `L ⊗[K] ker φ` of `φ_L : l ⊗ a ↦ l · φ a`. So `y` factors
  through `L`, and it equals `b ↦ |φ_L b|`.

## Hypotheses

`K : Type u` and `L : Type u'` are nontrivially normed fields that are
ultrametric (`IsUltrametricDist`) and complete, and `L` is a normed `K`-algebra
(`NormedAlgebra K L`). So `K → L` preserves norms. `A : Type v` is a commutative
`K`-algebra with a finite polynomial presentation
`P : FinitePolynomialPresentation K A`. The universes `u`, `u'` and `v` are
independent. The extension `L` need not be finite over `K`. No norm on `A` and no
nonemptiness, reducedness or positive arity are assumed.

## Statement

Write `baseChangePresentation K L P` for the published presentation of
`L ⊗[K] A` over `L` by the generators `1 ⊗ xₜ`. Write `baseChangeMap K L P` for
the published continuous map from its analytification
`Space L (baseChangePresentation K L P)` to `Space K P`. On seminorms it is
restriction along `Algebra.TensorProduct.includeRight : a ↦ 1 ⊗ a`.

1. `baseChangeMap K L P` is surjective.
2. Let `φ : AlgPoint K A K` be a `K`-rational point, and let
   `analyticPoint K P φ` be the published point of `Space K P` defined by `φ`.
   Let `φ_L : L ⊗[K] A →ₐ[L] L` be the image of the `L`-valued point
   `AlgPoint.mapCoefficients (Algebra.ofId K L) φ`, that is `a ↦ φ a` viewed in
   `L`, under Mathlib's equivalence
   `Algebra.TensorProduct.liftEquivRight K L A L`. So `φ_L (l ⊗ a) = l · φ a`.
   Then the preimage of the singleton `{analyticPoint K P φ}` under
   `baseChangeMap K L P` is the singleton
   `{analyticPoint L (baseChangePresentation K L P) (AlgPoint.ofAlgHom φ_L)}`.

Item (2) says both that the analytic point of `φ_L` maps to the analytic point
of `φ`, and that no other point of `(X_L)^an` does.

## Scope

The module supplies no proof; the statement is proved as
`affineAnalytificationBaseChange` in `AffineAnalytificationBaseChangeProof`.
It imports the published `AffineAnalytificationScalarExtension` and
`AffineAnalytificationRationalPoints` modules. It does not state that
`baseChangeMap` is proper, closed or a quotient map. It does not identify
`(X_L)^an` with a completed ground-field extension `X^an ⊗̂ L`, and it does not
describe the fibres over points that are not `K`-rational. It does not treat the
more general `extensionMap` for an arbitrary `K`-algebra map, scheme-level base
change, or independence of the presentation.

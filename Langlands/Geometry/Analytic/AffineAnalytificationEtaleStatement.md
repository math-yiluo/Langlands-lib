# Statement: affine analytification detects unramified, flat quasifinite and étale maps

`AffineAnalytificationEtaleStatement` states that a map of finitely presented
algebras is unramified, flat and quasi-finite, or étale exactly when the
induced map of polynomial-locus analytifications has the analytic property of
the same name. The analytic properties are the Library's
`AffinoidAtlasPresentation.StrongHom.IsUnramified`, `IsFlat` and `IsEtale` of
`FullRecognitionEtaleMorphisms`. It is a `Prop`-valued definition; this module
supplies no proof. It imports the published modules
`AffineAnalytificationLocalizedMap` and `FullRecognitionEtaleMorphisms`.

## Provenance

Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993),
registered as `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`:

- Definition 3.1.1, printed p.54/PDF p.51, defines finiteness at a point and
  quasifinite morphisms of analytic spaces. Corollary 3.1.7, printed
  p.56/PDF p.53, states that a morphism of schemes locally of finite type over
  `Spec(𝒜)`, for a `k`-affinoid algebra `𝒜`, is quasifinite if and only if its
  analytification is. Quasifinite scheme morphisms are those whose points are
  isolated in their fibres ([SGA1], 1.2, recalled on the same page).
- Definition 3.2.5, printed p.59/PDF p.56, defines flat quasifinite
  morphisms. Proposition 3.2.10, printed p.60/PDF p.57: such a morphism of
  schemes "is flat quasifinite if and only if the corresponding morphism
  `φᵃⁿ` is flat quasifinite".
- Definition 3.3.4, printed p.63/PDF p.60: a quasifinite morphism is
  unramified if `Ω_{Y/X} = 0`, and étale if it is unramified and flat.
  Proposition 3.3.11, printed p.64/PDF p.61: such a morphism of schemes "is
  unramified (resp. étale) if and only if the corresponding morphism `φᵃⁿ` is
  unramified (resp. étale)".

The case used here is the base `𝒜 = k`, that is, schemes locally of finite type
over the ground field.

Berkovich, *Spectral Theory and Analytic Geometry over Non-Archimedean Fields*
(1990), Proposition 3.4.6, printed p.65/PDF p.79, states the same
equivalences for flat, unramified and étale morphisms in the sense of that
book, which does not require quasifiniteness. The registered source is
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
SHA256 `9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`.
The Library's notions follow Berkovich 1993, so the 1993 propositions are the
ones transcribed.

Conrad, *Weil and Grothendieck approaches to adelic points* (2011), printed
p.19, proof of Proposition 5.11(3), uses the analytification of [CT]
(Conrad–Temkin) in the sense of rigid-analytic spaces. He describes it as
compatible with "étale maps", among other things, and uses that "rigid-analytic
étale maps are local isomorphisms near rational points". The registered source
is `conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

The statement is a derived formulation of the affine case of Berkovich's
propositions for the Library's polynomial-locus model. The algebraic
properties of `Spec(B) → Spec(A)` are expressed with Mathlib's predicates on
the ring map `f`:

- Unramified: `RingHom.FormallyUnramified`, the vanishing of `Ω[B⁄A]`. Since
  `B` is of finite type over `K`, it is of finite type over `A`, so this is
  unramifiedness of the scheme morphism.
- Quasifinite: `RingHom.QuasiFinite`, finite-dimensionality of every fibre
  algebra `κ(p) ⊗[A] B`. For finite-type algebras this is equivalent to finite
  fibres, the scheme notion of quasifiniteness for a morphism of affine
  schemes of finite type.
- Flat: `RingHom.Flat`.
- Étale: `RingHom.Etale`, that is, `Algebra.Etale` for the algebra structure
  given by `f`.

The Library's analytic notions follow Berkovich 1993 with derived choices
described in `FullRecognitionEtaleMorphisms.md`. In particular, all three
include local finiteness of the morphism (Berkovich's quasifiniteness).

## Hypotheses

- `K : Type u` is a nontrivially normed, ultrametric, complete field.
- `A : Type v` and `B : Type w` are commutative `K`-algebras with finite
  polynomial presentations `P` and `Q`.
- `f : A →ₐ[K] B` is an arbitrary `K`-algebra map.

No other hypothesis is made. The algebras may be zero.

## The statement

Write `g := saturatedHom K P Q f`, the published morphism
`Spec(B)ᵃⁿ → Spec(A)ᵃⁿ` of saturated presentations. Its type is the type of
strong maps from `(presentation K Q).saturatedPresentation` to
`(presentation K P).saturatedPresentation`, which is the type on which the
Library's `IsUnramified`, `IsFlat` and `IsEtale` are defined. For all such
data, the following three equivalences hold.

1. `f.toRingHom.FormallyUnramified ↔ g.IsUnramified`.
2. `(f.toRingHom.Flat ∧ f.toRingHom.QuasiFinite) ↔ g.IsFlat`.
3. `f.toRingHom.Etale ↔ g.IsEtale`.

Here `g.IsUnramified` asks that `g` is unramified at every point, and
`g.IsFlat` that it is flat at every point. Both pointwise notions are in the
form of Berkovich's Proposition 3.2.3(a): open neighbourhoods between which `g`
is finite, and finitely many affinoid pieces over which the finite affinoid
maps are unramified, respectively flat, at the point. `g.IsEtale` is
`g.IsUnramified ∧ g.IsFlat`.

## Truth sketch

This is not a Lean proof. It follows Berkovich's proofs.

- Quasifiniteness. Berkovich 1993, Corollary 3.1.7: for every point `x` of
  `Spec(A)ᵃⁿ`, the fibre of `g` over `x` is the analytification of the fibre
  of `f` over the image of `x` in `Spec(A)`, after extending scalars to the
  completed residue field `ℋ(x)`. So `g` has finite fibres exactly when `f`
  does, and `g` is closed (Berkovich 1993, Proposition 2.6.1).
- Unramifiedness. The module of differentials of the analytification is the
  analytification of `Ω[B⁄A]`. The map `Spec(B)ᵃⁿ → Spec(B)` is surjective
  (Berkovich 1990, Theorem 3.4.1(i)), and its local rings are faithfully flat
  over those of `Spec(B)`. So `Ω[B⁄A]` vanishes if and only if the
  differentials of the finite affinoid pieces vanish at every point. An
  unramified morphism of finite type has finite fibres, so it is quasifinite.
- Flatness. For the converse direction, faithful flatness of the local rings
  of the analytifications over those of the schemes descends flatness. For
  the direct direction, Zariski's main theorem embeds `Spec(B)` openly into a
  scheme finite over `Spec(A)` (Berkovich 1993, proof of Proposition 3.2.10,
  using Proposition 2.6.10).
- Étaleness. Combine the two previous items. Mathlib's
  `RingHom.Etale.iff_flat_and_formallyUnramified` characterizes `f.Etale` as
  flat, formally unramified and of finite presentation; `f` has finite
  presentation because `A` and `B` are finitely presented over `K`. A formally
  unramified map of finite type is quasi-finite.

## Scope

The statement covers only affine schemes given by finite polynomial
presentations over the ground field `K`. It does not cover nonaffine schemes,
other bases, smoothness, local isomorphism near rational points, the
pointwise versions `IsUnramifiedAt`, `IsFlatAt` and `IsEtaleAt`, or the
morphism in the localized category. The analytic properties are properties of
the specific strong map `saturatedHom K P Q f`; their invariance under change
of presentation is not stated.

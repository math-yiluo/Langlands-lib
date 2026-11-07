# Local-to-relative Weil maps through the completed local class extension

Worker 248 wrote this definition unit for task
`241e7251-de0b-431f-83a9-5584e974e22b`, which asks for a proof of
`LocalRelativeWeilMapExistenceStatement`. All declarations are in the namespace
`Langlands.ClassField.Global.RelativeWeilGroup`. The module imports only
`Langlands.ClassField.Global.LocalRelativeWeilMap`.

The module reduces the global predicate `IsLocalRelativeWeilMap` to two
properties of a map into a local object. It does not construct that local map
and does not assert that one exists. Its existence is the local
Weil–Shafarevich step and remains a separate prerequisite.

## Setting

Fix number fields `F E : Type u` with `[Algebra F E]` and `[IsGalois F E]`, and
a class family `c : FundamentalClass.ClassFamily.{u}`. Fix finite places
`v : Langlands.Global.FinitePlace F` and `w : Langlands.Global.FinitePlace E`
with `[w.asIdeal.LiesOver v.asIdeal]`, and
`[IsGalois (padicField v).Carrier (w.adicCompletion E)]`. Also fix the following
data.

- `I : ∀ p [Fact p.Prime], InvariantFamily.{u, u} p`, with
  `h : FundamentalClass.LocalCompatibility I c`.
- `a : CompletionH2 v w`, a class in `H²(Gal(E_w/F_v), E_wˣ)`, together with
  `ha`, a proof that `a` is a fundamental class for the relative invariant
  `(I (residuePrime v)).relative (padicField v) (w.adicCompletion E)`.

These are exactly the hypotheses of the published
`RelativeWeilGroup.localToRelative c v w I h a ha`. That is a continuous
homomorphism `CompletionClassExtension v w a →ₜ* RelativeWeilGroup c F E`.
Its source is the published extension of `Gal(E_w/F_v)` by `E_wˣ` for the chosen
representative of `a`. The local instance `completionGaloisTopology` gives
`Gal(E_w/F_v)` its discrete topology, as in the published modules.

## Declarations

- `continuous_krull_of_relativeGalois c f hf`. Here `f : X → RelativeWeilGroup c F E`
  is a map from a topological space, and `hf` says that `f` is continuous when
  `Gal(E/F)` carries `relativeGaloisTopology F E`, the discrete topology `⊥`.
  The conclusion is that `f` is continuous for the default topology on
  `RelativeWeilGroup c F E`, in which `Gal(E/F)` carries Mathlib's Krull
  topology. The two topologies on `Gal(E/F)` are equal: the Krull topology on
  the Galois group of a finite extension is discrete, so `DiscreteTopology.eq_bot`
  identifies it with `⊥`. The proof rewrites along this equality. This lemma is
  needed because `localToRelative` is published with `relativeGaloisTopology` on
  its target, while `IsLocalRelativeWeilMap` uses the default topology.
- `localWeilToRelative c v w I h a ha κ`. Here
  `κ : Weil.Local.localWeilGroup (padicField v) →ₜ* CompletionClassExtension v w a`.
  The definition is the composite `localToRelative c v w I h a ha ∘ κ`, as a
  continuous homomorphism
  `Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E` for the
  default topology on the target. Its underlying monoid homomorphism is the
  composite of the two underlying monoid homomorphisms. Continuity comes from the
  composite of the two continuity proofs, for `relativeGaloisTopology`, followed by
  `continuous_krull_of_relativeGalois`.
- `localWeilToRelative_apply` states, by `rfl`, that
  `localWeilToRelative c v w I h a ha κ g = localToRelative c v w I h a ha (κ g)`.
- `isLocalRelativeWeilMap_localWeilToRelative c v w I h a ha e he κ hP hR`
  concludes `IsLocalRelativeWeilMap v w e (localWeilToRelative c v w I h a ha κ)`
  from the following hypotheses.
  - `e : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField v w)` and
    `he`, its geometric normalization
    `LocalClassField.GeometricWeilReciprocityRelation (towerPadicField v w)
    (towerPadicField v w).canonicalTopologicalData e`.
  - `hP`: for all `g : W_{F_v}` and `y : E_w`,

    `j(projection(κ g)(y)) = σ_g(j(y))`,

    where `j = completionClosureEmbedding v w : E_w → \bar{F_v}`,
    `projection = CompletionClassExtension.projection v w a`, and
    `σ_g = Weil.Local.localProjection (padicField v) g`, applied as an algebra
    homomorphism. So the image of `κ g` in `Gal(E_w/F_v)` acts on `E_w` as the
    Galois image of `g` does, through `j`.
  - `hR`: for all `y : W_{E_w}`,

    `κ(completionWeilMap v w y) = (CompletionClassExtension.inclusion v w a (e[y]))⁻¹`,

    where `e[y] = LocalFactor.RankOne.reciprocityUnits (towerPadicField v w) e y`.

## Proof of `isLocalRelativeWeilMap_localWeilToRelative`

`IsLocalRelativeWeilMap` has three conditions.

1. The first condition is the geometric normalization of `e`, which is `he`.
2. The second condition asks, for `g : W_{F_v}` and `x : E`, that
   `j(x_w(projection c F E (ι g) x)) = σ_g(j(x_w(x)))`, where
   `x_w = algebraMap E (w.adicCompletion E)`. After `localWeilToRelative_apply`,
   the published `projection_localToRelative` replaces the global projection by
   `FundamentalClass.decompositionHom v w (projection(κ g))`. The published
   `algebraMap_decompositionHom` turns
   `x_w(decompositionHom v w τ x)` into `τ(x_w(x))`. The goal is then `hP g (x_w x)`.
3. The third condition asks, for `y : W_{E_w}`, that
   `ι(completionWeilMap v w y) = (inclusion c F E (i_w(e[y])))⁻¹`, where
   `i_w = IdeleClassGroup.ofAdicCompletion (𝓞 E) E w`. The proof rewrites with
   `localWeilToRelative_apply`, then `hR`, then `map_inv`, and finally the
   published `localToRelative_inclusion`. That lemma states
   `localToRelative (inclusion v w a x) = inclusion c F E (i_w x)`.

## Use

For the proof of `LocalRelativeWeilMapExistenceStatement`, the remaining input is
a map `κ` satisfying `hP` and `hR` for some fundamental class `a`. Such a class
exists by the published `InvariantFamily.fundamentalClasses_of_relativeImages`,
and the local Galois instance comes from the published `isGalois_adicCompletion`.
Worker 1237 is drafting the existence of `κ` as the separate statement
`LocalWeilClassMapExistenceStatement`. This module does not depend on it.

## Provenance

This is a derived construction. Tate, (1.6.1), states that a continuous
homomorphism `θ_v : W_{F_v} → W_F` exists and is compatible with the local and
global reciprocity maps. His proof, on printed pp.8–9, is the one-sentence remark
that the argument is analogous to (1.3.1) and (1.5.1). It uses the standard
relationship between global and local canonical classes and the vanishing of
`H¹(Gal(E_v/F_v), C_E)`. The factorization here follows that remark at the level
of a finite Galois extension `E/F`. The published `localToRelative` is the map of
extensions induced by the local-global class compatibility. `κ` is the local
Weil-group map that the remark leaves implicit. The hypotheses `hP` and `hR` are
the local forms of conditions 2 and 3 of the published predicate. The sign
convention in `hR` is that of `IsLocalRelativeWeilMap`, which its own Markdown
explains.

- J. Tate, *Number theoretic background*, Proc. Sympos. Pure Math. 33, Part II
  (1979), source `tate-1979-number-theoretic-background`, SHA256
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
  (1.6.1) and the sentence after it, printed pp.8–9 (PDF pp.17–18).

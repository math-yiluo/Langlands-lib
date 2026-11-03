# Statement: affineness descends along an arbitrary field extension

Author: Worker 770.

This module states that a scheme over a field `k` is affine whenever its base
change to some extension field `K` of `k` is affine. It defines the proposition
and proves nothing. The declaration is a `Prop`-valued `def` in the namespace
`Langlands.AlgebraicGeometry`, with one universe parameter `u`.

## Lean statement

```lean
def FieldExtensionAffineDescentStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k)),
    IsAffine (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) → IsAffine X
```

The module imports only `Mathlib.AlgebraicGeometry.Pullbacks`. It uses Mathlib's
`IsAffine`, `pullback` and `Spec.map` directly and introduces no new definitions.

- `k` and `K` are arbitrary fields in the same universe `u`, and `[Algebra k K]`
  is an arbitrary `k`-algebra structure on `K`. A ring map between fields is
  injective, so this makes `K` an extension field of `k`. The extension can be
  of any kind: finite or infinite, algebraic or transcendental, separable or
  inseparable. The statement makes no assumption on the characteristic.
- `X : Scheme.{u}` is an arbitrary scheme, and `f : X ⟶ Spec k` is an arbitrary
  morphism, the structure morphism of `X` over `k`. There is no
  quasi-compactness, quasi-separatedness, separatedness or finite-type premise
  on `X` or `f`. The empty scheme is included. Its base change is empty, and
  the empty scheme is affine (it is the spectrum of the zero ring), so the
  statement holds there for any `K`.
- `Spec.map (CommRingCat.ofHom (algebraMap k K)) : Spec K ⟶ Spec k` is the
  morphism of spectra induced by the extension. The scheme
  `pullback f (Spec.map ...)` is Mathlib's fibre product
  `X ×_{Spec k} Spec K`, that is, the base change `X_K` of `X` to `K`.
- Mathlib's `IsAffine Y` says that the canonical morphism
  `Y ⟶ Spec Γ(Y, ⊤)` is an isomorphism.
- The only hypothesis is affineness of `X_K`, as an explicit implication.
  No descent datum, no isomorphism `X ≅ Spec A`, no qcqs property of `X` and no
  comparison of global sections is assumed. These are what a proof must
  establish.

## Source and provenance

Provenance: derived. The proposition is the special case, for the fpqc covering
`{Spec K → Spec k}`, of the Stacks Project lemma that affineness is fpqc local
on the base. The source is the Stacks Project chapter *Descent*, PDF version
ed88ff78 compiled July 14, 2026 (source ID `stacks-descent-ed88ff78-2026`,
SHA-256 `28e718bac216bb7c4584e9edb1d25d6420ee19a6cd536742c58599242ff8cad4`). The
numbers below are those printed in this chapter PDF; the tags identify the
results in every edition.

- Lemma 23.20 (tag 02L5, PDF pp. 57–58): "The property P(f) = 'f is affine'
  is fpqc local on the base." Its proof treats the affine case: "let
  g : S′ → S be a flat surjective morphism of affine schemes, and let
  f : X → S be a morphism. Assume that the base change f′ : X′ → S′ is
  affine. In other words, X′ is affine, say X′ = Spec(A′). Also write
  S = Spec(R) and S′ = Spec(R′). We have to show that X is affine."
  Take `S = Spec k`, `S′ = Spec K` and `g = Spec K → Spec k`. Then `g` is flat,
  because every `k`-module is free and hence flat. It is surjective, because
  `Spec k` is a single point and `Spec K` is nonempty. Both schemes are
  affine. So this step of the proof, for an arbitrary morphism `f : X → Spec k`,
  is exactly the proposition above: affineness of `X′ = X_K` implies
  affineness of `X`. The source phrases its hypothesis and conclusion as
  affineness of the morphisms `f′` and `f`. Over affine bases this is the same
  as affineness of the schemes `X′` and `X`, as the quoted sentences say.
- Definition 22.1 (tag 02KO, PDF p. 52): `P` is fpqc local on the base if,
  for every fpqc covering `{Y_i → Y}` and every `f : X → Y`, `f` has `P` if and
  only if each base change `Y_i ×_Y X → Y_i` has `P`. Our proposition is the
  direction from the base changes back to `f`, for the one-element covering.
- Section 6 (tag 0CDQ, PDF p. 19): "Let k′/k be a field extension. Then
  {Spec(k′) → Spec(k)} is an fpqc covering." This is the covering used here,
  with no restriction on the extension.

The source proof first shows that `X → S` is quasi-compact and separated
(Lemmas 23.1, tag 02KQ, and 23.6, tag 02KU). It then identifies the base
change of `Γ(X, 𝒪_X)` with `Γ(X′, 𝒪_{X′})` by flat base change, and descends
the isomorphism `X → Spec Γ(X, 𝒪_X)` (Lemma 23.19, tag 02L4). These are
steps of the proof, not hypotheses of the statement.

## Relation to existing results

- The published theorem
  `AlgebraicGeometry.isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat`
  (module
  `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat`)
  is a different result. It assumes that `X` is quasi-compact and
  quasi-separated (`CompactSpace X`, `QuasiSeparatedSpace X`). For a flat
  `k`-algebra `A` it concludes only that global sections commute with base
  change: the square with corners `k`, `Γ(X, ⊤)`, `A` and `Γ(X_A, ⊤)` is a
  pushout of commutative rings. It says nothing about affineness and does not
  apply to an arbitrary `X`. The present statement assumes no qcqs property
  and concludes that `X` is affine. The pushout theorem can serve as the
  flat-base-change step of a proof, once quasi-compactness and
  quasi-separatedness of `X` have been proved.
- Mathlib's `AlgebraicGeometry.descendsAlong_isomorphisms_surjective_inf_flat_inf_quasicompact`
  (`Mathlib/AlgebraicGeometry/Morphisms/FlatDescent.lean`) descends
  isomorphisms along flat, surjective, quasi-compact morphisms. Mathlib has no
  descent of affineness or of affine morphisms along faithfully flat maps.
  `Mathlib/AlgebraicGeometry/Morphisms/Descent.lean` lists this as a TODO. So
  the pinned Mathlib does not prove this proposition.

## Use

The finite Galois splitting proof for field tori (task
`0f874577-70f6-49b9-8a37-b4797a0eeab6`) needs this proposition. The Library's
`IsTorus` gives only some field extension over which the torus splits, so the
group scheme is affine after that base change. This proposition then gives
affineness over the base field. A separate `lean.proof@1` task must prove it.

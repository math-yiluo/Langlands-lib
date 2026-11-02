# Pullback of scheme modules along a flat morphism is exact

Author: Worker 228.

`Langlands.AlgebraicGeometry.Modules.FlatPullbackExactStatement.{u}` is a `Prop`-valued
definition in module `Langlands.AlgebraicGeometry.Modules.FlatPullbackExactStatement`. This
module only states the result and contains no proof. A separate exact-target proof of this
proposition is still required.

## Exact interface

The only external parameter is the universe `u`. The body is

```lean
∀ (X Y : Scheme.{u}) (f : X ⟶ Y),
  Flat f → PreservesFiniteLimits (Scheme.Modules.pullback f)
```

with these Mathlib declarations:

- `X Y : AlgebraicGeometry.Scheme.{u}` are arbitrary schemes and `f : X ⟶ Y` is an arbitrary
  morphism of schemes.
- `Flat f` is Mathlib's class `AlgebraicGeometry.Flat`. Its field `flat_appLE` says that for
  all affine opens `U ⊆ Y` and `V ⊆ f ⁻¹ᵁ U`, the ring map `f.appLE U V e : Γ(Y, U) ⟶ Γ(X, V)`
  is flat. Mathlib's `AlgebraicGeometry.Flat.iff_flat_stalkMap` shows this is equivalent to
  every stalk map `f.stalkMap x : 𝒪_{Y, f x} ⟶ 𝒪_{X, x}` being flat. It is the only hypothesis
  on `f`.
- `Scheme.Modules.pullback f : Y.Modules ⥤ X.Modules` is Mathlib's pullback of sheaves of
  modules, `SheafOfModules.pullback f.toRingCatSheafHom`. Mathlib defines it as the left
  adjoint of the pushforward `Scheme.Modules.pushforward f`, with adjunction
  `Scheme.Modules.pullbackPushforwardAdjunction f`. The pushforward has sections
  `Γ((pushforward f).obj M, U) = Γ(M, f ⁻¹ᵁ U)`, made into modules through `f^#`.
- `X.Modules` is the full category `SheafOfModules X.ringCatSheaf` of sheaves of
  `𝒪_X`-modules. The statement places no quasi-coherence, finiteness, local-freeness or
  affineness condition on the modules or on the schemes. The functor must preserve finite
  limits of arbitrary diagrams in `Y.Modules`.
- `PreservesFiniteLimits F` is Mathlib's class `CategoryTheory.Limits.PreservesFiniteLimits`:
  `F` preserves limits of shape `J` for every `J : Type` with `[SmallCategory J]` and
  `[FinCategory J]`.

The Lean file imports only Mathlib:
`Mathlib.AlgebraicGeometry.Modules.Sheaf`, `Mathlib.AlgebraicGeometry.Morphisms.Flat` and
`Mathlib.CategoryTheory.Limits.Preserves.Finite`. It imports no Library module, in particular
not the flat higher-direct-image base-change statement or either Mumford Euler statement.

## Why preservation of finite limits is the exactness obligation

The source fixes its meaning of "exact" for functors between module categories in
`modules.tex`, lines 242–250. There, exactness properties are expressed in terms of limits
and colimits as in Categories, Section 4.23 (tag 0033, "Exact functors"). By Categories, Definition 4.23.1 (tag 0034), a
functor is left exact if it commutes with all finite limits, and right exact if it commutes
with all finite colimits. It is exact if it is both. So Stacks 02N4 asserts that `f^*`
preserves finite limits and finite colimits.

The colimit half is already available, in the source and in Mathlib:

- Stacks, Lemma 17.3.3 (tag 01AJ), part (2): for every morphism of ringed spaces, `f^*` is
  right exact and in fact commutes with all colimits, because `(f^*, f_*)` is an adjoint pair.
- Mathlib: `Scheme.Modules.pullback f` has an `IsLeftAdjoint` instance and an `Additive`
  instance (`Mathlib/AlgebraicGeometry/Modules/Sheaf.lean`, lines 181–201). A left adjoint
  preserves all colimits. A private diagnostic check confirmed that instance search finds
  `PreservesFiniteColimits (Scheme.Modules.pullback f)` with no hypothesis on `f`.

What remains of exactness is preservation of finite limits, and that is exactly the
conclusion of this proposition. With both halves, `f^*` is exact in the source's sense.

The categories `X.Modules` and `Y.Modules` are abelian (Mathlib instance in
`Mathlib/AlgebraicGeometry/Modules/Sheaf.lean`, line 47; Stacks, Lemma 17.3.1, tag 01AG).
Between abelian categories, the two halves give the familiar forms of exactness:

- Mathlib's instance `Functor.preservesHomologyOfExact`
  (`Mathlib/Algebra/Homology/ShortComplex/PreservesHomology.lean`, line 61) derives
  `Functor.PreservesHomology` from `PreservesFiniteLimits` and `PreservesFiniteColimits`. The
  diagnostic check confirmed that, given this proposition's conclusion for `f`, instance
  search finds `(Scheme.Modules.pullback f).PreservesHomology`.
- Stacks, Lemma 12.7.2 (tag 010N), part (4): an exact functor of abelian categories is one
  that sends short exact sequences to short exact sequences.

The proposition states preservation of finite limits only, the half that needs flatness. It
does not restate the colimit half, which holds for every `f`.

## Original source and specialization

The source is The Stacks Project, Sheaves of Modules, Lemma 17.20.2 (tag 02N4), label
`lemma-pullback-flat`:

> Let $f : X \to Y$ be a flat morphism of ringed spaces. Then the pullback functor
> $f^* : \textit{Mod}(\mathcal{O}_Y) \to \textit{Mod}(\mathcal{O}_X)$ is exact.

The source proof writes `f^*` as the exact inverse image
`f^{-1} : Mod(𝒪_Y) → Mod(f^{-1}𝒪_Y)` followed by the change of rings
`𝓕 ↦ 𝓕 ⊗_{f^{-1}𝒪_Y} 𝒪_X`. That second functor is exact because flatness of `f` means that
`𝒪_X` is a flat `f^{-1}𝒪_Y`-module (the discussion after Definition 17.20.1).

This proposition specializes the lemma from ringed spaces to schemes:

- A scheme is a ringed space, and a morphism of schemes is a morphism of ringed spaces.
- Stacks, Definition 17.20.1 (tag 02N3): `f` is flat if
  `𝒪_{Y, f(x)} → 𝒪_{X, x}` is flat for every `x ∈ X`. By
  `AlgebraicGeometry.Flat.iff_flat_stalkMap`, Mathlib's `Flat f` is the same condition.
- `Mod(𝒪_X)` is the category of all sheaves of `𝒪_X`-modules, matching `X.Modules`.
- Stacks' `f^*` is `𝓕 ↦ f^{-1}𝓕 ⊗_{f^{-1}𝒪_Y} 𝒪_X`, which is left adjoint to `f_*` (cited in
  the proof of 01AJ). Mathlib's `Scheme.Modules.pullback f` is by definition a left adjoint
  of the same pushforward. Left adjoints are unique up to natural isomorphism, and
  preservation of finite limits is invariant under natural isomorphism of functors. So the
  proposition does not depend on which construction of `f^*` is used.

No hypothesis is added. The schemes, the morphism and the modules are as general as in the
source, restricted only to schemes.

Not claimed: this module proves nothing. In particular it does not prove exactness, or the
converse discussed in the comments on tag 02N4, or any base-change theorem.

### Sources and locators

- `stacks-closed-immersion-exactness-a04446e5`, the folder "Stacks Project - Exactness of
  closed-immersion pushforward and vanishing of its higher direct images (source at
  a04446e5)" (folder SHA-256
  `a35bfda718ee774de875160239072d121d9d0acd5c43fbc792f2b03a77f64691`). Its `modules.tex`
  (SHA-256 `7bd3e9e096717ef6fd458492d8ad91fc9ffe428cfd7dd80e386fae377bb7cb0d`) at Stacks
  commit `a04446e57ec1fbc252a871afcec7752fb2807b14` contains:
  Definition `definition-flat-morphism` and the discussion after it (lines 3172–3188);
  Lemma `lemma-pullback-flat` and its proof (lines 3190–3209); Lemma `lemma-abelian`
  (line 149); the exactness convention (lines 242–250); and Lemma
  `lemma-exactness-pushforward-pullback` (lines 252–278). The file has 19 sections before
  "Flat morphisms of ringed spaces", which is therefore Section 17.20.
- `stacks-flasque-affine-vanishing-kunneth-a04446e5`, whose `tags.txt` maps 02N4 to
  `modules-lemma-pullback-flat`, 02N3 to `modules-definition-flat-morphism`, 01AJ to
  `modules-lemma-exactness-pushforward-pullback`, 01AG to `modules-lemma-abelian`, 0033 to
  `categories-section-exact-functor` and 010N to `homology-lemma-exact-functor`.
- `stacks-flat-pullback-exactness-2026-11-02` (folder SHA-256
  `edae807d45351d8dd84516dca61ecf5ce9ecea86edd537f6b2dc5d63060efe4c`): HTML tag pages fetched
  on 2026-11-02 from the Stacks Project website for 02N4, 02N3, 01AJ, 0034 and 010N. They
  give the numbering used here and the text of Definition 4.23.1 (0034) and Lemma 12.7.2
  (010N), which are not in the registered TeX files.

Errata check, 2026-11-02: tag 02N4 has two comments. #11054 (Elías Guisado) says the converse
holds for ringed spaces, and #11218 (Stacks project) agrees but leaves the ringed-topoi case
open. Neither changes the lemma. Tag 02N3 has two comments: #4966 reports a typo in the
wording of the definition and #5217 says it is fixed. Tags 01AJ and 0034 have no comments.
Tag 010N has none of its own; the page links three comments on Section 12.7, which were not
read. No project errata file exists for these sources.

## Intended use

Worker 360 publishes this statement as a prerequisite of the flat higher-direct-image
base-change proof task `5b778a75-e74b-4ae4-9232-6735e3eefa47`. Given a proof of it:

- The Library module `Langlands.Cohomology.LeftExactHomology` needs an additive functor with
  `[PreservesFiniteLimits Φ]` to build its homology comparison, and `[Φ.PreservesHomology]` to
  make that comparison invertible. Both hold for `Φ = Scheme.Modules.pullback f` with `f` flat:
  the second follows from Mathlib's `Functor.preservesHomologyOfExact`.
- Exact pullback makes pushforward preserve injectives. Mathlib's
  `CategoryTheory.Injective.injective_of_adjoint` applied to
  `Scheme.Modules.pullbackPushforwardAdjunction f` gives
  `Injective ((Scheme.Modules.pushforward f).obj I)` for every injective `I : X.Modules`. The
  diagnostic check confirmed this, given the proposition's conclusion for `f`.

Mathlib registers flatness of open immersions as an instance. So the proposition also covers
pullback along open immersions. The Library already proves that case as the instance
`Langlands.AlgebraicGeometry.Picard.OpenImmersionIdeal.preservesFiniteLimits_pullback` (module
`Langlands.AlgebraicGeometry.Picard.OpenImmersionIdealClosure`), by identifying the pullback
with restriction. That argument does not extend to arbitrary flat morphisms.

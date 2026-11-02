# Pullback of scheme modules preserves quasi-coherence

Author: Worker 1038.

`Langlands.AlgebraicGeometry.Modules.QuasicoherentPullbackStatement.{u}` is a `Prop`-valued
definition. This module only states the result; it contains no proof. A separate
exact-target proof of this proposition is still required.

The module imports only Mathlib (`Mathlib.AlgebraicGeometry.Modules.Sheaf` and
`Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`). It imports no Library module.

## Exact interface

The only parameter is the universe `u`. The proposition is

```lean
∀ (X Y : Scheme.{u}) (f : X ⟶ Y) (M : Y.Modules),
  M.IsQuasicoherent →
    ((Scheme.Modules.pullback f).obj M).IsQuasicoherent
```

It quantifies over the following data, in this order.

- Schemes `X Y : Scheme.{u}`. This is Mathlib's `AlgebraicGeometry.Scheme`. Nothing more
  is assumed about `X` or `Y`.
- A morphism of schemes `f : X ⟶ Y`. It has no hypotheses. In particular `f` need not be
  flat, affine, quasi-compact, separated, of finite type or an open immersion.
- A module `M : Y.Modules`. `Y.Modules` is Mathlib's `AlgebraicGeometry.Scheme.Modules Y`,
  defined as `SheafOfModules.{u} Y.ringCatSheaf`. Its objects are the sheaves of modules
  over the structure sheaf `𝒪_Y`, on the site of open subsets of `Y`. The module `M` need
  not be of finite type, finitely presented or locally free.
- The hypothesis `M.IsQuasicoherent`. This is Mathlib's class
  `SheafOfModules.IsQuasicoherent`. It holds when there is a `QuasicoherentData M`. Such
  data consist of:
  - a family of opens `U i` of `Y` that covers the terminal object for the Grothendieck
    topology of `Y`, that is, the `U i` cover `Y`;
  - for each `i`, a presentation of `M.over (U i)`, the restriction of `M` to `U i`,
    viewed as a sheaf of modules over the restricted structure sheaf.

  Each presentation has two parts. The first is a family of generating sections, indexed
  by a type in `Type u`, so that the induced morphism from the free module onto
  `M.over (U i)` is an epimorphism. The second is a family of generating sections of the
  kernel of that morphism. So `M` restricted to `U i` is the cokernel of a morphism
  `⨁_{j ∈ J} 𝒪_{U i} ⟶ ⨁_{k ∈ K} 𝒪_{U i}` of free modules.

The conclusion is `((Scheme.Modules.pullback f).obj M).IsQuasicoherent`. This is the same
Mathlib class for the `𝒪_X`-module `f^*M`. Here `Scheme.Modules.pullback f` is Mathlib's
`AlgebraicGeometry.Scheme.Modules.pullback f`, defined as
`SheafOfModules.pullback f.toRingCatSheafHom`. That is the chosen left adjoint of the
pushforward functor `Scheme.Modules.pushforward f`; the adjunction is
`Scheme.Modules.pullbackPushforwardAdjunction f`.

A private check confirmed the declaration and these constants. Unfolding the definition
and then using reducible `rfl` matches it with the displayed term, written with fully
qualified Mathlib names `AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme.Modules`,
`AlgebraicGeometry.Scheme.Modules.pullback` and `SheafOfModules.IsQuasicoherent`.

The statement assumes no data: no cover of `X` or `Y`, no presentation and no
comparison isomorphism. The hypothesis `M.IsQuasicoherent` is the only assumption.

## Original source and specialization

The sources are from the Stacks Project at git commit
`a04446e57ec1fbc252a871afcec7752fb2807b14`. They are in the registered folder
`stacks-closed-immersion-exactness-a04446e5` (folder SHA-256
`a35bfda718ee774de875160239072d121d9d0acd5c43fbc792f2b03a77f64691`), file `modules.tex`
(SHA-256 `7bd3e9e096717ef6fd458492d8ad91fc9ffe428cfd7dd80e386fae377bb7cb0d`). The
same-commit `tags.txt` maps tag 01BG to `modules-lemma-pullback-quasi-coherent` (line
1725) and tag 01BE to `modules-definition-quasi-coherent` (line 1723). This file is in the
registered folder `stacks-flasque-affine-vanishing-kunneth-a04446e5` (folder SHA-256
`af02e6f0aff875e216f1e0fde58f6baad3eedeb6b82799a8d6c91ff68cccaa3a`).

The cited result is Sheaves of Modules, Lemma 17.10.4, `lemma-pullback-quasi-coherent`
(tag 01BG). Its label is at line 1086, the statement at lines 1085–1091 and the proof at
lines 1093–1124:

> Let f : (X, O_X) → (Y, O_Y) be a morphism of ringed spaces. The pullback f^*G of a
> quasi-coherent O_Y-module is quasi-coherent.

Lemma, definition and chapter numbers are those on the Stacks website, checked on
2026-11-02. The tags and LaTeX labels identify the results at the cited commit.

This task specializes the lemma from ringed spaces to schemes, as follows.

- The source's morphism of ringed spaces is the underlying morphism of a morphism of
  schemes `f : X ⟶ Y`. Every morphism of schemes has one. The Lean statement covers
  exactly this case. It says nothing about ringed spaces that are not schemes, or about
  morphisms of ringed spaces that do not come from morphisms of schemes.
- The source's `O_Y`-modules are the objects of `Y.Modules`, the Mathlib category of
  sheaves of `𝒪_Y`-modules on the opens of `Y`.
- The source's quasi-coherence is Definition 17.10.1, `definition-quasi-coherent`
  (tag 01BE, label at line 1021, lines 1020–1034). Every point has an open
  neighbourhood `U` such that `F|_U` is isomorphic to the cokernel of a map
  `⨁_{j ∈ J} O_U → ⨁_{i ∈ I} O_U`. The Lean statement uses Mathlib's
  `SheafOfModules.IsQuasicoherent`, described above, in both the hypothesis and the
  conclusion. The index types of its covering family and its presentations live in
  `Type u`, the universe of the sections.
- The source's pullback `f^*G` is the module pullback of ringed spaces. Its adjunction
  `(f^*, f_*)` is the one cited in the proof of Lemma 17.3.3,
  `lemma-exactness-pushforward-pullback` (tag 01AJ, label at line 253, adjunction cited
  at line 271). The Lean statement uses Mathlib's `Scheme.Modules.pullback f`, which is
  defined as a left adjoint of the same pushforward. Two left adjoints of one functor are
  canonically isomorphic, and the Lean conclusion is about this particular choice.

The quantifiers match the source: one statement for every morphism `f`, and for every
quasi-coherent module `G = M` on the target.

The source's proof, for orientation only: arguing as in Lemma 17.8.2,
`lemma-pullback-locally-generated` (tag 01B3, label at line 749), restrict to opens `V`
of `Y`. There `f^*G|_{f^{-1}V} ≅ (f')^*(G|_V)` for the restricted morphism
`f' : f^{-1}V → V`. So one may assume that `G` has a global presentation
`⨁_J O_Y → ⨁_I O_Y → G → 0`. Since `f^*` is right exact and commutes with all colimits
(Lemma 17.3.3), applying `f^*` gives a presentation `⨁_J O_X → ⨁_I O_X → f^*G → 0`. The
step `f^* O_Y = O_X` is used implicitly. A Lean proof may follow a different route.

Errata: the tag page of 01BG, fetched on 2026-11-02 and registered as
`stacks-tag-01BG-page-2026-11-02` (SHA-256
`f68bf1a4192d956d97ff7493ae1c8696d66b89432f25a8dfeb14285cf2537c6a`), has no comments.
It notes two comments on Section 17.10. The page did not show their text, and this
statement does not depend on them. No project errata file exists for these sources.

## Related Library results and intended use

The Library already has two special cases of this statement. Neither covers its full
scope.

- `Langlands.Scheme.Modules.isQuasicoherent_affinePullback`, in module
  `Langlands.AlgebraicGeometry.Modules.AffinePullbackQuasicoherent`. It covers
  `Spec.map φ` for a ring map `φ`.
- `Langlands.AlgebraicGeometry.Picard.IsLocallyFreeRankOne.isQuasicoherent_pullback`, in
  module `Langlands.AlgebraicGeometry.Picard.LineBundleQuasicoherent`. It covers locally
  free modules of rank one.

This statement is a prerequisite for the flat base-change proof task
`5b778a75-e74b-4ae4-9232-6735e3eefa47`. That task must extend the Čech line-bundle
base-change argument to arbitrary quasi-coherent modules, and it needs `f^*M` to be
quasi-coherent for every quasi-coherent `M`. This module does not establish that
base-change result or this theorem.

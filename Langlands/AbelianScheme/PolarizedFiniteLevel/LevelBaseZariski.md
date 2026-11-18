# Zariski opens, sheaves and open charts on the level base category

This internal module adds Zariski vocabulary for the published category
`LevelBase n`. Its objects are the universe-zero locally noetherian schemes on
which the integer `n` is a unit, with all scheme morphisms. The module
introduces no moduli content and asserts no theorem beyond the elementary
facts stated below.

## Opens of a level base

- `LevelBase.level_isUnit_open S U`: for an open `U` of a level base `S`, the
  integer `n` is a unit in `Γ(U, ⊤)`. It is the image of the unit `n` of
  `Γ(S, ⊤)` under the ring map `U.ι.appTop`, since ring maps preserve natural
  number casts.
- `LevelBase.ofOpen S U` is the open subscheme `U.toScheme` as an object of
  `LevelBase n`. Mathlib's instance gives local noetherianity of open
  subschemes; the previous lemma gives the unit condition.
- `LevelBase.openι S U : S.ofOpen U ⟶ S` is the open inclusion `U.ι`.
- `LevelBase.openLE S h : S.ofOpen U ⟶ S.ofOpen V` is Mathlib's inclusion
  `S.obj.homOfLE h` of nested opens `U ≤ V`.
- `LevelBase.openLE_openι` records `openLE h ≫ openι V = openι U`, from
  Mathlib's `Scheme.homOfLE_ι`.

## Zariski sheaves

`LevelBase.IsZariskiSheaf F`, for a presheaf `F : (LevelBase n)ᵒᵖ ⥤ Type v`,
says the following. Let `S` be a level base and `U : ι → S.obj.Opens` a family
of opens indexed by a type `ι : Type` with `iSup U = ⊤`. Let `s i` be sections
of `F` over the opens `S.ofOpen (U i)` that agree on overlaps: the restrictions
of `s i` and `s j` to `S.ofOpen (U i ⊓ U j)` along the two `openLE` inclusions
are equal. Then there is a unique section `t` over `S` whose restriction along
`openι (U i)` is `s i` for every `i`. This is the usual sheaf condition for
open covers, stated for the test category `LevelBase n`, whose objects are
closed under passage to open subschemes.

## Open charts

Let `F : (LevelBase n)ᵒᵖ ⥤ Type 1` and `X : LevelBase n`. A natural
transformation `a : uliftYoneda.{1}.obj X ⟶ F` from the lifted functor of
points of `X` is an open chart, `LevelBase.IsOpenChart a`, when two conditions
hold.
- Each component `a.app T` is injective, so `a` identifies the functor of
  points of `X` with a subfunctor of `F`.
- For every level base `S` and section `ξ ∈ F(S)` there is an open `U` of `S`
  with the following property. For every level base `T` and morphism
  `f : T ⟶ S`, the pullback `F.map f.op ξ` lies in the image of `a.app T`
  exactly when the set-theoretic image of `f` lies in `U`.

The second condition expresses the hypothesis "each `F_i ⊂ F` is representable
by open immersions" of the Stacks Project, Schemes, Lemma 26.15.4 (tag 01JJ),
in the form used in its proof: `T → S` factors through the open `U` exactly
when `ξ` restricted to `T` lies in the subfunctor. Here the factorization is
tested set-theoretically, on morphisms from level bases.

`LevelBase.IsOpenChartCover a`, for a family `a i : uliftYoneda.{1}.obj (X i) ⟶ F`
indexed by `ι : Type`, says the charts cover `F`. For every level base `S`,
section `ξ ∈ F(S)` and point `x` of `S`, some index `i` and some open `U`
containing `x` satisfy the open-chart condition for `ξ` and `a i`.

## Provenance

These definitions are internal adaptations of the hypotheses of the Stacks
Project, Chapter 26, Section 26.15, Lemma 26.15.4 (tag 01JJ), registered as
`stacks-open-chart-representability-2026-11-01`. They are restricted to the
published test category `LevelBase n` and its lifted functors of points with
values in `Type 1`, which are the conventions of the published
`moduliFunctor` and `LargeLevelRepresentabilityStatement`.

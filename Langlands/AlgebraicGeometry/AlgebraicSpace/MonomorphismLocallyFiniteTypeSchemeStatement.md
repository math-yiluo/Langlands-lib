# Schemeness of algebraic spaces with a locally finite type monomorphism to a scheme

Author: Worker 303.

This module states that an algebraic space with a monomorphism, locally of
finite type, to a scheme is represented by a scheme. This combines Stacks Project
Lemma 67.27.10 (Tag 0463) with Proposition 67.50.2 (Tag 03XX). Local finite type
is asked of one surjective etale scheme atlas. The module contains one
proposition definition and no proof. It imports the published
`Langlands.AlgebraicGeometry.AlgebraicSpace.Basic`, unchanged, and Mathlib's
`Mathlib.AlgebraicGeometry.Morphisms.FiniteType` for `LocallyOfFiniteType`.

## The statement

In namespace `Langlands.AlgebraicGeometry.AlgebraicSpace`,
`MonomorphismLocallyFiniteTypeSchemeStatement.{u} : Prop` is

```lean
∀ (S : Scheme.{u}) (X : AlgebraicSpace S) (Y : Over S)
  (f : X.presheaf ⟶ (schemeYoneda S).obj Y), Mono f →
  (∃ (W : Over S) (a : (schemeYoneda S).obj W ⟶ X.presheaf) (w : W ⟶ Y),
    IsEtale a ∧ IsSurjective a ∧ a ≫ f = (schemeYoneda S).map w ∧
      LocallyOfFiniteType w.left) →
  IsRepresentedByScheme X
```

Except for Mathlib's `LocallyOfFiniteType`, every name comes from `Basic`:

- `AlgebraicSpace S` is the published category of algebraic spaces over `S`.
  Its objects are fppf sheaves on `Over S` with values in `Type (u + 1)`, with
  representable diagonal and a surjective etale scheme atlas. `X.presheaf` is
  the underlying presheaf of `X`.
- `schemeYoneda S` is the lifted Yoneda functor `Over S ⥤ Presheaf S`.
  `(schemeYoneda S).obj Y` is the functor of points of the scheme `Y` over
  `S`, and `(schemeYoneda S).map w` is the natural transformation induced by
  `w : W ⟶ Y` in `Over S`.
- `f` is a natural transformation of presheaves on `Over S`.
  `Mono f` is a monomorphism in the presheaf category `Presheaf S`.
- `IsEtale a` and `IsSurjective a` are the published predicates. Each says that
  `a` is representable by schemes, and that in every represented pullback
  square along a map from a scheme, the scheme projection is etale (resp.
  surjective).
- `LocallyOfFiniteType w.left` is Mathlib's predicate for the underlying
  morphism of schemes `w.left : W.left ⟶ Y.left`.
- `IsRepresentedByScheme X` is
  `∃ U : Over S, Nonempty ((schemeYoneda S).obj U ≅ X.presheaf)`. It asks for
  an actual scheme over `S` and an actual natural isomorphism from its functor
  of points to the presheaf of `X`.

## Quantifiers and what is not assumed

The proposition quantifies universally over the base scheme `S`, the algebraic
space `X`, the scheme `Y` over `S` and the transformation `f`. It has two
hypotheses: that `f` is a monomorphism, and that some surjective etale atlas
`a` of `X` composed with `f` is induced by a scheme morphism `w` that is locally
of finite type. The conclusion only asserts that some scheme represents `X`.
Nothing relates the representing scheme to `Y`, `f`, `W` or `a`.

The universe `u` is arbitrary. There is no quasi-compactness,
quasi-separatedness, separatedness, noetherian, finite type or affineness
hypothesis on `S`, `Y`, `X`, `W` or on any of the morphisms. `X` is any
algebraic space in the convention of `Basic`, which has no quasi-compactness
condition on the diagonal. The hypothesis does not ask that `f` is separated
or locally quasi-finite. In the source these properties follow from the
hypotheses by Lemma 67.27.10.

The hypothesis asks for local finite type on a single atlas. It does not ask
it for every etale chart. By the equivalence explained below, this is the same
as `f` being locally of finite type in the Stacks sense. A statement with the
hypothesis for every atlas would be weaker, and would follow from this one,
since every algebraic space has some surjective etale atlas.

## Original source and translation

The registered source is `stacks-mono-lft-schemehood-2026-11-02`, a Stacks
Project HTML snapshot retrieved on 2 November 2026. It holds the pages of
Tags 03XX, 0463, 042L, 042M, 03XF and 03MJ. All are in Chapter 67, Morphisms of
Algebraic Spaces.

[Lemma 67.27.10, Tag 0463](https://stacks.math.columbia.edu/tag/0463), line 173
of `0463.html`:

> Let $S$ be a scheme. Let $f : X \to Y$ be a morphism of algebraic spaces over
> $S$. If $f$ is locally of finite type and a monomorphism, then $f$ is
> separated and locally quasi-finite.

[Proposition 67.50.2, Tag 03XX](https://stacks.math.columbia.edu/tag/03XX),
line 173 of `03XX.html`:

> Let $S$ be a scheme. Let $f : X \to T$ be a morphism of algebraic spaces over
> $S$. Assume $T$ is representable, $f$ is locally quasi-finite, and $f$ is
> separated. Then $X$ is representable.

Applying the lemma and then the proposition to a monomorphism locally of
finite type $f : X \to Y$ with $Y$ a scheme gives the composite assertion: $X$
is representable. The Lean proposition states this composite. It is weaker than
Proposition 67.50.2 in general: it covers only those separated locally
quasi-finite morphisms that are monomorphisms locally of finite type.

The page of 03XX has one comment (#688, 13 June 2014). It reports a missing
word in "algebraic spaces over" in this proposition and in the previous lemma.
It does not affect the mathematics. The pages of 0463, 042L, 042M, 03XF and 03MJ
have no comments. No errata note for this source was found in the project, in
the current Library or in the workspace `notes/errata/` locations.

The translation is as follows.

- *Let $S$ be a scheme; algebraic spaces over $S$.* This is `S : Scheme.{u}`
  and `X : AlgebraicSpace S`, the fppf-sheaf convention of `Basic`. The target
  scheme $T$ (called $Y$ in 0463) is `Y : Over S`, viewed as an algebraic space
  through its functor of points `(schemeYoneda S).obj Y`. Morphisms of
  algebraic spaces in `Basic` are exactly natural transformations of the
  underlying presheaves (`homEquiv`). So `f` is a morphism of algebraic spaces
  from `X` to `Y`.
- *Monomorphism.* Definition 67.10.1 (Tag 042L) calls a morphism of algebraic
  spaces a monomorphism if it is an injective map of sheaves, that is, a
  monomorphism in the category of sheaves on $(\mathit{Sch}/S)_{fppf}$.
  Lemma 67.10.2 (Tag 042M) adds that this is equivalent to being a
  monomorphism in the category of algebraic spaces. Lean asks `Mono f` in the
  presheaf category. Both `X.presheaf` and `(schemeYoneda S).obj Y` are fppf
  sheaves, the second because the fppf topology is subcanonical. For a map
  between sheaves, being a monomorphism of presheaves, a monomorphism of
  sheaves and injective on all sections are equivalent. Monomorphisms of
  presheaves are checked objectwise, and the inclusion of sheaves into
  presheaves is fully faithful and a right adjoint. This comparison is
  informal background and is not formalized here.
- *Locally of finite type.* Definition 67.23.1 (Tag 03XF) says $f$ is locally
  of finite type if the equivalent conditions of Lemma 67.22.1 (Tag 03MJ) hold
  for the property "locally of finite type". Condition (2) of 03MJ asks for
  one commutative square $h : U \to V$ over $f$, where $U$ and $V$ are schemes,
  $a : U \to X$ and $b : V \to Y$ are etale, and $a$ is surjective, such that
  $h$ is locally of finite type. The Lean hypothesis is condition (2) with
  $V = Y$ and $b$ the identity, $U = W$, and $h = w$. The equation
  `a ≫ f = (schemeYoneda S).map w` is the commutativity of the square.
  Conversely, condition (1) of 03MJ says every such square has $h$ locally of
  finite type. Apply it to $V = Y$ with any surjective etale atlas $a$ of $X$,
  which exists since $X$ is an algebraic space. The composite `a ≫ f` is
  `(schemeYoneda S).map w` for a unique `w`, by full faithfulness of the lifted
  Yoneda functor. Hence the Lean hypothesis is equivalent to $f$ being locally
  of finite type in the Stacks sense. The etale and surjective conditions on
  `a` use the scheme-test convention of `Basic` for representable
  transformations. This equivalence is informal background and is not
  formalized here.
- *$X$ is representable.* An algebraic space over $S$ is representable when
  it is isomorphic to the functor of points of a scheme over $S$. This is
  `IsRepresentedByScheme X`.

## Provenance

The proposition is derived. It is the composite of two source results: Lemma
67.27.10 (0463) supplies separatedness and local quasi-finiteness of `f`, and
Proposition 67.50.2 (03XX) then gives representability. It is stated in this
form because Langlands has no predicates for separated or locally
quasi-finite morphisms of algebraic spaces, while monomorphisms and local
finite type on an atlas can be expressed with published and Mathlib notions.

## Intended use

The statement is a prerequisite of the proof of
`Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothRelationQuotientStatement`
(task `947bc5d5-327d-4b44-91e8-22c7382f065b`). There, an arrow algebraic space
`R` with `s t : R.presheaf ⟶ (schemeYoneda S).obj U` is injective on sections
through `(s, t)` and has a surjective etale atlas `b` with
`b ≫ s = (schemeYoneda S).map s₀` and `b ≫ t = (schemeYoneda S).map t₀` for
smooth `s₀.left` and `t₀.left`. The plan is to apply this statement with
`Y` the product `U ⨯ U` in `Over S`, `f` the pair `(s, t)` composed with the
comparison of `(schemeYoneda S).obj (U ⨯ U)` with the product of functors of
points, and `w` the pair `(s₀, t₀)`. The morphism `w.left` is locally of finite
type because its composite with the first projection is the smooth morphism
`s₀.left`. That application is a plan and is not part of this unit.

## Status and scope

This unit states the proposition only. Its proof is a later separate
candidate or exact-target task, after this statement is in the Library. The
unit formalizes neither Lemma 67.27.10 nor Proposition 67.50.2 separately,
and it defines no separated or locally quasi-finite morphisms of algebraic
spaces.

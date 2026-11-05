# Structural atlas geometry agrees with scheme geometry on actual schemes

Authors: Worker 840, with Worker 139 (author of the task objective, which
specifies the proposition body used verbatim here).

This module states the compatibility obligation between the published
one-atlas predicates of
`Langlands.AlgebraicGeometry.AlgebraicSpace.StructuralAtlasGeometry` and
Mathlib's scheme properties, for schemes viewed as algebraic spaces. It
contains one Prop-valued definition and no proof. It imports the published
`Langlands.AlgebraicGeometry.AlgebraicSpace.StructuralAtlasGeometry`
unchanged. That module imports
`Langlands.AlgebraicGeometry.AlgebraicSpace.Basic` and Mathlib's
`Mathlib.AlgebraicGeometry.Morphisms.Smooth`, so all names used below are
available through this one import.

## The statement

In namespace `Langlands.AlgebraicGeometry.AlgebraicSpace`,
`StructuralAtlasSchemeCompatibilityStatement.{u} : Prop` is

```lean
∀ (S : Scheme.{u}) (U : Over S),
  (SmoothOverBase ((schemeToSpace S).obj U) ↔
    Smooth U.hom) ∧
  (LocallyOfFinitePresentationOverBase ((schemeToSpace S).obj U) ↔
    LocallyOfFinitePresentation U.hom) ∧
  (LocallyOfFiniteTypeOverBase ((schemeToSpace S).obj U) ↔
    LocallyOfFiniteType U.hom)
```

In words: for every scheme `S` and every scheme `U` over `S`, the algebraic
space defined by `U` is smooth over `S` in the one-atlas sense if and only if
the structure morphism of `U` is smooth. The same holds for local finite
presentation and for local finite type. A development check confirmed that
`Smooth`, `LocallyOfFinitePresentation` and `LocallyOfFiniteType` elaborate to
Mathlib's `AlgebraicGeometry.Smooth`,
`AlgebraicGeometry.LocallyOfFinitePresentation` and
`AlgebraicGeometry.LocallyOfFiniteType`.

## Meaning of the names

- `S : Scheme.{u}` is an actual scheme. `U : Over S` is an actual scheme
  `U.left : Scheme.{u}` together with its structure morphism
  `U.hom : U.left ⟶ S`.
- `schemeToSpace S : Over S ⥤ AlgebraicSpace S` is the published fully
  faithful inclusion of schemes over `S` into algebraic spaces over `S`
  (module `Basic`). The object `(schemeToSpace S).obj U` is the algebraic
  space whose underlying fppf sheaf is the functor of points of `U`. Its
  presheaf is `(schemeYoneda S).obj U`, the lifted Yoneda functor of `U`, with
  values in `Type (u + 1)`. It is the actual scheme `U` itself, embedded. The
  statement does not posit a representing scheme for an arbitrary algebraic
  space.
- `SmoothOverBase X`, `LocallyOfFinitePresentationOverBase X` and
  `LocallyOfFiniteTypeOverBase X` are the published predicates
  `HasAtlasProperty P X` with `P` equal to Mathlib's `Smooth`,
  `LocallyOfFinitePresentation` and `LocallyOfFiniteType`, respectively.
  `HasAtlasProperty P X` is

  ```lean
  ∃ (W : Over S) (a : (schemeYoneda S).obj W ⟶ X.presheaf),
    IsEtale a ∧ IsSurjective a ∧ P W.hom
  ```

  (the published source names the atlas scheme `U`; it is renamed `W` here to
  avoid a clash with the `U` of the statement). So the left side of each
  equivalence says: there is an actual scheme `W` over `S` and an actual
  natural transformation `a` from the functor of points of `W` to that of
  `U`, such that `a` is etale and surjective, and the structure morphism
  `W.hom : W.left ⟶ S` has the scheme property. Since `a` is a
  transformation of presheaves on schemes over `S`, `W.hom` is the
  composite of the atlas with the structural morphism of the space to `S`.
  (By full faithfulness `a` comes from a morphism `w : W ⟶ U` over `S`, and
  `W.hom = w.left ≫ U.hom`; the statement does not mention `w`.)
- `IsEtale a` and `IsSurjective a` keep their published meanings from
  `Basic`. Each says that `a` is representable by actual schemes and that,
  in every represented pullback square of `a` along a map from the functor
  of points of a scheme, the scheme projection is etale (respectively
  surjective). Surjectivity is geometric surjectivity of these projections.
  It does not mean surjectivity on sections.
- On the right, `Smooth U.hom`, `LocallyOfFinitePresentation U.hom` and
  `LocallyOfFiniteType U.hom` are the pinned Mathlib properties of the actual
  morphism `U.hom : U.left ⟶ S`. Mathlib defines each one affine-locally: for
  every affine open `V ⊆ S` and affine open `V' ⊆ U.hom ⁻¹ V`, the ring map
  `Γ(S, V) ⟶ Γ(U.left, V')` is smooth, of finite presentation, or of finite
  type, respectively.

## Quantifiers and what is not assumed

The proposition quantifies over every scheme `S` and every scheme `U` over `S`
in one arbitrary universe `u`. There is no affineness, reducedness,
noetherianity, quasi-separatedness, quasi-compactness, dimension, finite type
or projectivity hypothesis on `S`, `U.left` or `U.hom`, and no hypothesis on
the atlases.

The three equivalences are separate conjuncts, and none assumes another.
In particular the local finite presentation and the local finite type
equivalences hold without any smoothness assumption. A consumer may use any
one conjunct on its own.

## What is already available and what remains

The direction from the scheme property to the atlas predicate is already
published for each conjunct: `SmoothOverBase.of_scheme`,
`LocallyOfFinitePresentationOverBase.of_scheme` and
`LocallyOfFiniteTypeOverBase.of_scheme` use `U` itself with the identity
transformation as atlas. A private development check confirmed that these
three lemmas give the right-to-left implications of the statement.

The converse, from some surjective etale atlas `a` with the property on
`W.hom` to the property of `U.hom`, is the substantive remaining obligation.
It is an etale descent argument: `a` comes from a morphism of schemes
`w : W ⟶ U` that is etale and surjective, and the property descends from
`W.hom = w.left ≫ U.hom` to `U.hom`. This unit states that obligation and
proves nothing. Its proof is a separate later exact-target proof task for
this unchanged proposition.

## Original sources and translation

The registered source `stacks-mono-lft-schemehood-2026-11-02` (content
SHA-256 `dcc9a958ea2cec87994a4191d6e3969d1c0f4836266a827082cf9ce42c249df3`)
contains `03MJ.html` and `03XF.html`. The registered source
`stacks-structural-atlas-geometry-2026-11-03` (content SHA-256
`8c3f10b49df7e2195ce78f4f98c54e89277749fb3149aabdf3117023515f65da`)
contains `03ZC.html`, `03ZB.html`, `03XP.html` and `03XO.html`. All are pages
of Chapter 67, Morphisms of Algebraic Spaces, of the Stacks Project.

[Lemma 67.22.1, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ): for a
property $\mathcal{P}$ of morphisms of schemes which is etale local on the
source-and-target, a morphism $f : X \to Y$ of algebraic spaces over $S$,
and commutative squares $h : U \to V$ over $f$ with $U$, $V$ schemes and
etale vertical arrows $a : U \to X$, $b : V \to Y$, the following are
equivalent: (1) for every such square $h$ has $\mathcal{P}$; (2) for some
such square with $a$ surjective $h$ has $\mathcal{P}$. The lemma continues:

> If $X$ and $Y$ are representable, then this is also equivalent to $f$ (as a
> morphism of schemes) having property $\mathcal{P}$.

[Definition 67.37.1, Tag 03ZC](https://stacks.math.columbia.edu/tag/03ZC),
[Definition 67.28.1, Tag 03XP](https://stacks.math.columbia.edu/tag/03XP) and
[Definition 67.23.1, Tag 03XF](https://stacks.math.columbia.edu/tag/03XF)
define $f$ to be smooth, locally of finite presentation, and locally of
finite type, respectively, when the equivalent conditions of Lemma 67.22.1
hold with $\mathcal{P}$ the corresponding property of morphisms of schemes.
[Lemma 67.37.4(6), in Section 67.37, Tag 03ZB](https://stacks.math.columbia.edu/tag/03ZB)
and [Lemma 67.28.4(6), in Section 67.28, Tag 03XO](https://stacks.math.columbia.edu/tag/03XO)
add the one-atlas criteria: $f$ is smooth (respectively locally of finite
presentation) if and only if there exist a scheme $U$ and a surjective etale
morphism $\varphi : U \to X$ such that $f \circ \varphi$ is smooth
(respectively locally of finite presentation).

The translation to the Lean statement is as follows.

- Take for $f$ the structure morphism of the space to the base, so $Y$ is
  the scheme $S$, and take for $X$ the algebraic space given by the scheme
  `U`, which is `(schemeToSpace S).obj U`. Both $X$ and $Y$ are then
  representable, and $f$ as a morphism of schemes is `U.hom`. So the last
  sentence of Lemma 67.22.1 identifies the Stacks property of $f$ with
  Mathlib's property of `U.hom`. This is the right side of each equivalence.
- The published predicates on the left take $V = S$ and $b$ the identity in
  the square of Lemma 67.22.1, so $h$ is the composite structure morphism
  `W.hom` of the atlas scheme. They are exactly the one-atlas criteria (6)
  of Lemmas 67.37.4 and 67.28.4 with $U$ there the atlas scheme `W`. For
  local finite type the cited sources give no separately numbered one-atlas
  criterion, but the predicate is condition (2) of Lemma 67.22.1 with
  $V = S$, $b$ the identity, and it lies between conditions (1) and (2),
  because the identity of `U` is a surjective etale atlas.
- Combining the two points, for these three properties the Stacks Project
  asserts that the left and right sides of each equivalence agree for every
  scheme over every scheme base. The proposition states this for each
  property separately.
- Stacks defines etale and surjective morphisms from a scheme to an
  algebraic space through representability and base change to schemes. The
  published `IsEtale` and `IsSurjective` follow that convention with actual
  scheme tests. This comparison is informal background, recorded with the
  published definitions, and is not formalized here.

## Provenance

The proposition is an internal, derived compatibility statement between the
Library's existential chart definitions, its actual scheme embedding and
Mathlib's scheme geometry. No cited source states this exact Lean
proposition. Its mathematical content is the representable (scheme) case of
the chart criteria above, specialized to a scheme base. The form with three
independent conjuncts, all scheme bases and an arbitrary universe was
requested by the task contract and by its consumer feedback.

## Source reading record

The six HTML pages above, including their comments, were read in the
retained snapshots. Tag 03ZB has two comments: one reports that an old
occurrence of "syntomic" in the first sentence should read "smooth", and the
reply reports the fix. Tag 03XP has two comments: one reports that the
morphism label $f$ was missing at the beginning of the definition, and the
reply reports the fix. The retained texts contain the corrected wording.
Tags 03MJ, 03XF, 03XO and 03ZC have no comments of their own (03ZC links to
the two section comments of 03ZB). No source-specific errata note was found
in the project notes, the current Library notes and wiki, or the workspace.
The HTML pages are authoritative; the same-stem text files are mechanical
aids that omit formulas in script elements.

## Scope

The statement concerns only the three named properties and only spaces that
come from actual schemes. It asserts no atlas independence for arbitrary
algebraic spaces and no compatibility for an arbitrary `HasAtlasProperty P`.
It states no properness, Picard representer, group scheme, universal family
or actual-family comparison theorem. It changes no published definition and
does not touch the separately published representable relative predicate
`IsSmooth`, which includes scheme representability and is a different
predicate from `SmoothOverBase`.

## Intended use

This statement is a focused prerequisite of the finite-type smooth-family
representability task `90a7704e-771a-4107-a91a-c67873dd035e` (Worker 139).
That task retains the finite-type existence argument and the final assembly.

# Structural properties of algebraic spaces through scheme atlases

Author: Worker 1603.

This module defines three structural properties of an actual
`X : Langlands.AlgebraicGeometry.AlgebraicSpace S` over every
`S : Scheme.{u}` by existence of an actual surjective etale scheme atlas.
The definitions use the existing fppf-sheaf algebraic spaces and all actual
scheme tests. The base and spaces have no added reducedness, noetherianity,
quasi-separatedness or scheme-representability hypothesis.

## Original sources and specialization

The registered source `stacks-structural-atlas-geometry-2026-11-03`,
SHA-256 `8c3f10b49df7e2195ce78f4f98c54e89277749fb3149aabdf3117023515f65da`,
is the retained full HTML snapshot in
`literature/Stacks Project - Structural smoothness and local finite
presentation of algebraic spaces (HTML snapshot 2026-11-03)/`.
Its source references are:

- [Definition 67.37.1, Tag 03ZC](https://stacks.math.columbia.edu/tag/03ZC):
  smooth morphisms of algebraic spaces are defined by the etale
  source-and-target chart criterion.
- [Section 67.37, Tag 03ZB](https://stacks.math.columbia.edu/tag/03ZB),
  Lemma 67.37.4(6): smoothness can be tested by existence of a scheme
  `U` and a surjective etale `U → X` whose composite to the target is
  smooth. Lemmas 67.37.5 and 67.37.6 give the local finite presentation
  and local finite type implications.
- [Definition 67.28.1, Tag 03XP](https://stacks.math.columbia.edu/tag/03XP)
  and [Section 67.28, Tag 03XO](https://stacks.math.columbia.edu/tag/03XO),
  Lemma 67.28.4(6): the corresponding definition and one-atlas criterion
  for local finite presentation. Lemma 67.28.5 gives local finite type.

The reused registered source `stacks-mono-lft-schemehood-2026-11-02`,
SHA-256 `dcc9a958ea2cec87994a4191d6e3969d1c0f4836266a827082cf9ce42c249df3`,
is retained in
`literature/Stacks Project - Monomorphisms locally of finite type and
schemehood of separated locally quasi-finite algebraic spaces, Tags 03XX,
0463, 04/`. The relevant passages are
[Lemma 67.22.1, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
and [Definition 67.23.1, Tag 03XF](https://stacks.math.columbia.edu/tag/03XF).
They give the general source-and-target chart criterion for a property
that is etale local on source and target, and its specialization to local
finite type.

The six full original HTML pages, including their comments, were read.
Tag 03ZB's comments report the correction of an old syntomic/smooth typo;
Tag 03XP's comments report the correction of an omitted morphism label.
The retained definitions contain the corrected text. The other four pages
have no comments of their own. No source-specific errata note was present
in the checked project, current Library or workspace note locations.

Here the target of the structural morphism is the scheme `S` itself.
In the source-and-target chart diagram take the target chart to be the
identity `S → S`. An actual `U : Over S` then carries exactly the composite
`U.hom : U.left ⟶ S`. The source chart is an actual transformation from
the scheme's functor of points to the entire presheaf of `X`.
The three named definitions use this scheme-base chart condition.
The generic wrapper and its elementary interfaces are internal derived
packaging; the sources do not define atlas-independent geometry for an
arbitrary scheme-morphism property.

## Exact definitions

All names below are in
`Langlands.AlgebraicGeometry.AlgebraicSpace`. For an arbitrary
`P : CategoryTheory.MorphismProperty Scheme.{u}`, the Prop-valued definition
`HasAtlasProperty P X` is exactly

```lean
∃ (U : Over S) (a : (schemeYoneda S).obj U ⟶ X.presheaf),
  IsEtale a ∧ IsSurjective a ∧ P U.hom
```

Thus it supplies the actual source scheme over the same base, the actual
natural transformation, both geometric properties, and the scheme
property of the source's structural morphism. `schemeYoneda S` is the
published lifted Yoneda functor. The presheaves are
`(Over S)ᵒᵖ ⥤ Type (u + 1)`; all test and atlas schemes remain in
`Scheme.{u}`. The transformations and isomorphisms act on this whole
category, including nonreduced and nonaffine tests.

`IsEtale a` and `IsSurjective a` retain their published meanings. Each
includes representability by actual schemes after every scheme base
change. Etaleness and surjectivity apply to every represented scheme
projection. Surjectivity is geometric surjectivity of those projections,
with no assertion of objectwise surjectivity on presheaf sections.

The three separate Prop-valued definitions specialize `P` as follows:

| Space predicate | Mathlib property required of `U.hom` |
| --- | --- |
| `SmoothOverBase X` | `AlgebraicGeometry.Smooth U.hom` |
| `LocallyOfFinitePresentationOverBase X` | `AlgebraicGeometry.LocallyOfFinitePresentation U.hom` |
| `LocallyOfFiniteTypeOverBase X` | `AlgebraicGeometry.LocallyOfFiniteType U.hom` |

These are the pinned Mathlib scheme properties, not new predicates on
the coordinate rings. Only the atlas map must be represented by schemes.
There is no requirement that the structural map of `X` be scheme-representable.
The existing representable relative predicate `IsSmooth` and the existing
`SmoothRelationQuotient.HasSmoothProjections` retain their separate meanings.

## Implemented elementary interfaces

`HasAtlasProperty.exists_atlas` exposes the defining witnesses.
`HasAtlasProperty.of_atlas` constructs the predicate from any supplied
actual atlas and proof of `P U.hom`. Each named specialization also has
an `exists_atlas` accessor with its exact scheme property.

`HasAtlasProperty.mono` accepts `hPQ : P ≤ Q`, meaning a pointwise
implication `P f → Q f` for every actual scheme morphism `f`. Its proof
keeps `U`, `a`, etaleness and geometric surjectivity unchanged and applies
`hPQ` only to `U.hom`.

`SmoothOverBase.locallyOfFinitePresentation` and
`LocallyOfFinitePresentationOverBase.locallyOfFiniteType` apply that lemma
using Mathlib's existing scheme-property instances. The implementation
locally installs the given proof of the stronger property as a typeclass
instance and asks for the weaker one.
`SmoothOverBase.locallyOfFiniteType` composes these two implications.
These elementary proofs keep the same atlas throughout, matching the
chartwise route of the cited Stacks implication lemmas.

`HasAtlasProperty.of_scheme U hU` uses `U` itself and the identity
transformation as atlas for `((schemeToSpace S).obj U)`. Mathlib's
`MorphismProperty.relative_map` applied to the identity scheme map
supplies geometric surjectivity, using the existing base-change-stability
instance for the property under `Over.forget S`. The published
`isEtale_map` supplies etaleness by the same represented-map mechanism.
Functoriality identifies the image of the identity scheme map with the
identity transformation.
No geometric property of `U.hom` beyond the explicit input `hU` is used.
Each named specialization has the corresponding `of_scheme` introduction.

For `e : X.presheaf ≅ Y.presheaf`, `HasAtlasProperty.of_iso` replaces
an atlas `a` by `a ≫ e.hom`, retaining exactly the same `U`, `U.hom`
and proof of `P U.hom`. It reuses the published `IsEtale.comp_iso`
and `IsSurjective.comp_iso` lemmas; their represented-pullback geometry
is not reproved. This generic transport also applies to the locally finite
type condition already transported by
`exists_locallyFiniteType_atlas_of_iso`, without redeveloping that fixed
property result. `HasAtlasProperty.iff_of_iso` applies the forward
transport to `e` and its inverse. Each of the three named predicates has
`of_iso` and `iff_of_iso` specializations. Neither monotonicity nor this
transport requires that `P` itself respect isomorphisms, because the
actual structure map is unchanged.

## Scope and remaining obligations

For arbitrary `P`, `HasAtlasProperty P X` asserts existence of one such
atlas only. It asserts no independence from the choice of atlas.
For the three named properties, the cited original chart criteria justify
this choice of definition. Lean equivalence with an all-atlas definition,
or the converse implication from a represented scheme's atlas predicate
to Mathlib's property of its own structural morphism, remains a separate
etale-descent obligation. The definitions and the forward identity-atlas
introductions do not prove that obligation.

The module contains only the existential definitions and the elementary
interfaces described above. It changes no existing space, Picard,
representability or finite-type statement, and establishes no properness,
quotient existence, Picard representer, abelian group existence or
substantive descent theorem.

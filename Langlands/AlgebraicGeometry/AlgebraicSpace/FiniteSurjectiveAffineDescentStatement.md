# Finite-surjective descent of affineness for algebraic spaces

Author: Worker 239.

This module states Stacks Project Lemma 70.15.1 (Tag 07VS): if a finite
surjective morphism of algebraic spaces over a scheme has a source that is an
affine scheme, then its target is an affine scheme. It states the lemma for
every base scheme and every such morphism, with no finite-presentation or
other extra hypothesis. It imports the published
`Langlands.AlgebraicGeometry.AlgebraicSpace.SchemeLocalGeometry` and uses its
predicates and those of `Basic` unchanged. It proves nothing.

## The proposition

In namespace `Langlands.AlgebraicGeometry.AlgebraicSpace`, the declaration
`FiniteSurjectiveAffineDescentStatement.{u} : Prop` is

```lean
def FiniteSurjectiveAffineDescentStatement : Prop :=
  ∀ (S : Scheme.{u}) (X Y : AlgebraicSpace S) (f : X ⟶ Y),
    IsFinite (hom f) → IsSurjective (hom f) →
      IsRepresentedByAffineScheme X → IsRepresentedByAffineScheme Y
```

It has the single universe parameter `u`. All four quantifiers are universal
and none is restricted:

- `S : Scheme.{u}` is an arbitrary scheme. It need not be affine,
  quasi-compact, quasi-separated, noetherian or reduced.
- `X Y : AlgebraicSpace S` are actual algebraic spaces over `S` in the
  fppf-sheaf convention of the published `Basic` module: fppf sheaves on
  schemes over `S` with values in `Type (u + 1)`, with representable diagonal
  and a geometrically surjective etale atlas by an actual scheme over `S`.
  No separatedness or quasi-compactness is assumed of `X`, `Y` or their
  diagonals, and `Y` is not assumed to be a scheme.
- `f : X ⟶ Y` is an actual morphism of algebraic spaces over `S`, and
  `hom f : X.presheaf ⟶ Y.presheaf` is its underlying natural transformation.
  The predicates below are the published ones for transformations of
  presheaves, applied to `hom f`.

The three hypotheses and the conclusion have the following meanings. All
names are those of the published modules.

- `IsFinite (hom f)` (from `SchemeLocalGeometry`) says that `hom f` is
  representable, and that for all `U V : Over S`, every
  `g : (schemeYoneda S).obj U ⟶ Y.presheaf`, every
  `a : (schemeYoneda S).obj V ⟶ X.presheaf` and every `p : V ⟶ U` forming a
  pullback square `IsPullback a ((schemeYoneda S).map p) (hom f) g`, the
  scheme morphism `p.left : V.left ⟶ U.left` is finite in Mathlib's sense
  (`AlgebraicGeometry.IsFinite`). Every represented square is tested, not
  only one chosen representability witness.
- `IsSurjective (hom f)` (from `Basic`) is the same construction with
  `AlgebraicGeometry.Surjective`: `hom f` is representable and every
  represented projection `p.left` is surjective on underlying points. It is
  geometric surjectivity, not surjectivity of a map of presheaves or
  sheaves.
- `IsRepresentedByAffineScheme X` (from `SchemeLocalGeometry`) means

  ```lean
  ∃ U : Over S, AlgebraicGeometry.IsAffine U.left ∧
    Nonempty ((schemeYoneda S).obj U ≅ X.presheaf)
  ```

  This asks for an actual scheme `U` over `S` and an actual natural
  isomorphism between its lifted Yoneda functor of points and the presheaf
  of `X`. The scheme `U.left` must be affine in Mathlib's absolute sense. No
  condition is placed on the structure morphism `U.hom : U.left ⟶ S`, so
  this is absolute affineness, not affineness of a morphism to `S`.
- The conclusion `IsRepresentedByAffineScheme Y` asks for the same two
  witnesses for `Y`: an actual scheme over `S` whose underlying scheme is
  affine, and an actual natural isomorphism with `Y.presheaf`.

A private development check confirmed by `rfl` that the declaration unfolds
to this formula with the fully qualified Langlands predicates
`Langlands.AlgebraicGeometry.AlgebraicSpace.IsFinite`, `.IsSurjective` and
`.IsRepresentedByAffineScheme`, not Mathlib's scheme predicates of the same
short names.

## Original source and translation

The statement is
[Lemma 70.15.1, Tag 07VS](https://stacks.math.columbia.edu/tag/07VS), in
Section 70.15 (Tag 07VQ), "Characterizing affine spaces", of Limits of
Algebraic Spaces. It is cited from the registered source
`stacks-algebraic-space-affine-descent-2026-11-01`, the Stacks Project HTML
snapshot of 1 November 2026 (directory SHA-256
`10fa51455958afc737851009364630c6f8e05ff49d790473a03fa1baaa4c00a0`).
The statement is at lines 163–165 of the retained `07VQ.html` and its proof
at lines 167–177:

> Let $S$ be a scheme. Let $f : X \to Y$ be a morphism of algebraic spaces
> over $S$. Assume that $f$ is surjective and finite, and assume that $X$ is
> affine. Then $Y$ is affine.

The whole retained Section 70.15, including its text aid `07VQ.txt` and its
single comment, was read. The comment (#1792) concerns a missing reference in
the proof of Proposition 70.15.2 and does not affect Lemma 70.15.1. No
source-specific errata note was found in the checked project, Library or
workspace locations.

The translation is as follows.

- *Let $S$ be a scheme; $f : X \to Y$ a morphism of algebraic spaces over
  $S$.* These are `S : Scheme.{u}`, `X Y : AlgebraicSpace S` and
  `f : X ⟶ Y`, with the conventions of `Basic`.
- *$f$ is finite.* Definition 67.45.2 (Tag 03ZP) of Morphisms of Algebraic
  Spaces, in the retained `03ZN.html` of the same registered source, calls
  $f$ finite if every base change $X \times_Y Z$ by an affine scheme
  $Z \to Y$ is representable by an affine scheme finite over $Z$.
  Lemma 67.45.3 (Tag 03ZQ) shows this is equivalent to $f$ being
  representable and finite in the scheme-test sense of Section 67.3, and
  Lemma 67.45.1 (Tag 03ZO) identifies that sense with the affine test. The
  scheme-test sense, testing every scheme base change, is the published
  `IsFinite`. The published `SchemeLocalGeometry` Markdown records this
  convention; it is not a Lean comparison theorem.
- *$f$ is surjective.* Definition 67.5.2 (Tag 03ME) calls a morphism of
  algebraic spaces surjective when $|f| : |X| \to |Y|$ is surjective.
  Lemma 67.5.3 (Tag 03MF) shows this is equivalent to every base change
  $Z \times_Y X \to Z$ by a scheme $Z$ being a surjective morphism of schemes,
  and Lemma 67.5.1 (Tag 03MD) makes the same identification for
  representable morphisms. These are cited from the registered source
  `stacks-algebraic-space-surjective-morphisms-2026-11-01`, the Stacks
  Project HTML snapshot of Section 67.5 (Tag 03MC) of 1 November 2026
  (directory SHA-256
  `2913d9742274ac9e357ea115d7170d006577593e6d6aa90dcd0f05beb1cb3dfd`):
  `03MC.html`, lines 163–173 (Lemma 67.5.1 with its proof), 178–180
  (Definition 67.5.2) and 183–223 (Lemma 67.5.3 with its proof). Its comment section is empty. The
  scheme-base-change form is the published `IsSurjective`. That predicate
  also contains representability of `hom f`, which already follows from
  `IsFinite (hom f)`. So under the finiteness hypothesis it imposes nothing
  beyond the source's surjectivity.
- *$X$ is affine; then $Y$ is affine.* An algebraic space over $S$ is
  affine when it is isomorphic to the functor of points of an affine scheme.
  In Lean this is `IsRepresentedByAffineScheme`, an internal specialization
  of the published `IsRepresentedByScheme` documented by the
  `SchemeLocalGeometry` module: the representing scheme must also be affine.
  Affineness is absolute, as in the source, where "$X$ is affine" refers to
  $X$ itself and not to its structure morphism to $S$.

## Hypotheses that are not assumed

The statement has no finite-presentation, finite-type, separatedness,
quasi-separatedness, quasi-compactness, noetherian or reducedness hypothesis
on `S`, `X`, `Y` or `f`. It does not assume that `Y` is already a scheme, and
it does not mention thickenings or their order. This matches the source,
whose statement has no such hypotheses.

The source's proof first deduces that $Y$ is separated and quasi-compact,
using that a finite morphism is affine and universally closed
(Lemma 67.45.7). It then reduces to finite presentation by limit arguments
(Lemmas 70.11.3, 70.5.10, Proposition 70.8.1, Lemmas 70.7.1, 70.6.7 and
70.6.4), and concludes by a cohomological criterion for spaces of finite
presentation over $\mathbf{Z}$ (Cohomology of Spaces, Lemma 69.17.3). These
steps are obligations of a later proof. They are neither hypotheses of this
statement nor results supplied by it.

## Status and scope

Development check: `lean_check` diagnostic
`f503496d-3e42-4c02-b197-69e7757b2556` compiled the module with 0 errors and
0 warnings; inspection reports a Prop-valued definition with level parameter
`u` and only the axioms `propext`, `Classical.choice` and `Quot.sound`.

This unit states the proposition only. Its exact proof is a separate later
task, published after this statement is accepted and in the Library. The
unit proves no descent result and no separatedness, quasi-compactness,
limit, approximation or cohomological lemma. It adds no definitions and
leaves the published `Basic`, `Thickening`, `SchemeLocalGeometry` and
`SchemenessOfThickeningStatement` Lean/Markdown pairs unchanged. It supplies
no open-subspace lifting or scheme gluing, no Picard deformation or
representability result and no comparison with an actual family.

It is a prerequisite of the general-thickening schemeness task
`1b18b90e-9748-4e50-a82b-c59bb05afe2c` (Workers 133 and 336), whose target
`SchemenessOfThickeningStatement` is unchanged. Their route applies this
statement to affine opens lifted across a thickening, using the published
`IsThickening.finite` and `IsThickening.surjective`.

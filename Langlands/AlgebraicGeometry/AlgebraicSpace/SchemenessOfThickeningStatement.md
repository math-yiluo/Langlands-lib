# Schemeness of algebraic spaces under arbitrary thickenings

Author: Worker 239.

This module states Stacks Project Lemma 76.9.5 (Tag 05ZR): if an algebraic
space `X'` is a thickening of an algebraic space `X` represented by a scheme,
then `X'` is also represented by a scheme. It contains one proposition
definition and no proof. It imports only
`Langlands.AlgebraicGeometry.AlgebraicSpace.Thickening`, which in turn imports
`Langlands.AlgebraicGeometry.AlgebraicSpace.Basic`. Both published modules are
used unchanged.

## The statement

In namespace `Langlands.AlgebraicGeometry.AlgebraicSpace`,
`SchemenessOfThickeningStatement.{u} : Prop` is

```lean
∀ (S : Scheme.{u}) (X X' : AlgebraicSpace S) (i : X ⟶ X'),
  IsThickening (hom i) →
    IsRepresentedByScheme X → IsRepresentedByScheme X'
```

Every name is the published one:

- `AlgebraicSpace S` is the actual category of algebraic spaces over `S` from
  `Basic`. Its objects are fppf sheaves on `Over S` with values in
  `Type (u + 1)`, with representable diagonal and a surjective etale scheme
  atlas. Its morphisms are morphisms of the underlying sheaves.
- `i : X ⟶ X'` is an actual morphism in this category, and `hom i` is its
  underlying natural transformation `X.presheaf ⟶ X'.presheaf`.
- `IsThickening (hom i)` is the published predicate from `Thickening`,
  `IsClosedImmersion (hom i) ∧ IsSurjective (hom i)`. It says that `hom i` is
  representable by schemes, and that for every represented pullback square
  `IsPullback a ((schemeYoneda S).map p) (hom i) g` with `U V : Over S`, the
  scheme projection `p.left : V.left ⟶ U.left` is a closed immersion that is
  surjective on points. No order bound is part of it.
- `IsRepresentedByScheme X` is the published predicate from `Basic`,
  `∃ U : Over S, Nonempty ((schemeYoneda S).obj U ≅ X.presheaf)`. It asks for
  an actual scheme over `S` and an actual natural isomorphism from its functor
  of points (with values lifted to `Type (u + 1)`) to the presheaf of `X`.

## Quantifiers and what is not assumed

The proposition quantifies universally over the base scheme `S`, both spaces
`X` and `X'` over `S`, and the morphism `i`. It has two hypotheses, that
`hom i` is a thickening and that `X` is represented by a scheme. The
conclusion is the existential `IsRepresentedByScheme X'`: some `U' : Over S`
and some natural isomorphism `(schemeYoneda S).obj U' ≅ X'.presheaf`.
Nothing relates the representing scheme of `X'` to that of `X` or to `i`; the
statement only asserts existence.

The universe `u` is arbitrary. The base `S` is any scheme in `Scheme.{u}`.
There is no assumption that the thickening has first order, `n`th order or
finite order; the published predicates `IsNthOrderThickening`,
`IsFirstOrderThickening` and `IsFiniteOrderThickening` are not used. There is
no reducedness, noetherian, finite type, quasi-compactness,
quasi-separatedness or affineness hypothesis on `S`, `X`, `X'`, on the
structure morphisms to `S`, or on `i`. Nothing is assumed about `X'` beyond
its being an algebraic space and the target of the thickening; in particular
the statement does not assume `X'` or any part of it is a scheme. The scheme
representing `X` need not be affine.

## Original source and translation

The registered source is `stacks-algebraic-space-thickenings-2026-11-01`,
the Stacks Project HTML snapshot retrieved on 1 November 2026. The statement
is [Lemma 76.9.5, Tag 05ZR](https://stacks.math.columbia.edu/tag/05ZR), in
Section 76.9 (Tag 05ZJ) of More on Morphisms of Spaces; it is lines 309–310
of the retained `05ZJ.html`:

> Let $S$ be a scheme. Let $X \subset X'$ be a thickening of algebraic spaces
> over $S$. If $X$ is (representable by) a scheme, then so is $X'$.

The page has no comments, and no errata note for this source was found in
the project, current Library or workspace `notes/errata/` locations.

The translation is as follows.

- *Let $S$ be a scheme.* This is `S : Scheme.{u}`, with no further
  condition. Algebraic spaces over `S` follow the fppf-sheaf convention
  implemented in `Basic` (Stacks Definition 65.6.1, Tag 025Y).
- *$X \subset X'$ a thickening.* Definition 76.9.1 in the same section calls
  `X'` a thickening of `X` if `X` is a closed subspace of `X'` and the
  associated topological spaces are equal. By Definition 65.12.1 (Tag 02YU), a
  closed subspace is a subfunctor whose inclusion is a closed immersion. The
  Lean statement expresses the closed-subspace notation by a morphism
  `i : X ⟶ X'` and the published predicate `IsThickening (hom i)`. This
  predicate uses the scheme-test convention of the introduction of
  Section 87.9 (Tag 0AI6): a representable morphism is a thickening when its
  represented scheme projections are closed immersions that are surjective on
  points, and Stacks observes there that this does not clash with
  Definition 76.9.1 when both are algebraic spaces. The translation of thickenings is that of the published
  `Thickening` module, whose Markdown records it.
- The inclusion of a closed subspace is such a morphism `i`, so the Lean
  statement covers the source's situation. It also allows a closed immersion
  `i` that is not literally a subfunctor inclusion. This is the same
  mathematical content: in the source, a closed immersion identifies its
  source with a closed subspace of its target, and representability by a
  scheme is invariant under isomorphism of spaces. This comparison is
  informal background; it is not formalized here.
- *$X$ is (representable by) a scheme; then so is $X'$.* An algebraic space
  over `S` is a scheme in the Stacks sense when it is isomorphic to the
  functor of points of a scheme over `S`. This is `IsRepresentedByScheme`,
  applied to `X` in the hypothesis and to `X'` in the conclusion.

## The unrestricted theorem and the finite-order proof

The source states the lemma for every thickening and gives two proofs. The
first proof is general: $X'_{red} = X_{red}$, so $X'_{red}$ is a scheme, and
the result follows from Limits of Spaces, Lemma 70.15.3 (Tag 07VU). The
source then gives a second, direct "proof for finite order thickenings",
which reduces to a first order thickening of an affine scheme and uses,
among others, Lemmas 76.9.3 and 76.9.4 (Tags 05ZP and 05ZQ) and Properties
of Spaces, Lemmas 66.13.1 and 66.33.1 (Tags 03JH and 05Z1). That second proof covers
only the special case; it does not restrict the lemma.

The Lean proposition is the unrestricted lemma, matching the source's
statement. A finite-order version would follow from it, since the published
`IsFiniteOrderThickening.thickening` turns a finite-order thickening into an
`IsThickening`; no such corollary is stated here. A proof of this
proposition must handle general thickenings, for example through reduction
and the source's Limits of Spaces route. Neither that route nor the
finite-order argument is formalized here.

## Status and scope

This unit states the proposition only. Its proof is a later separate
exact-target task, to be published after this statement is accepted and in
the Library. The unit proves nothing about reductions of algebraic spaces,
etale sites of thickenings, or the comparison between Definition 76.9.1 and
the scheme-test convention. It supplies no Picard deformation or
effectivity result, no Artin representability, no conductor gluing and no
comparison with an actual family.

It is a prerequisite of the finite-type representability task
`90a7704e-771a-4107-a91a-c67873dd035e` (Worker 139). That task's final
target and hypotheses are unchanged by this statement.

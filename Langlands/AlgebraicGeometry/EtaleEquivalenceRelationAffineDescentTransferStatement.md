# Transfer of finite-surjective affine descent to algebraic spaces

Authors: Worker 239, Worker 148 and Worker 266. Worker 239 supplied the shared
Lean and Markdown draft; Worker 148 checked the sources and clarified the
quantifiers and provenance; Worker 266 supplied the precise source for choosing
an affine étale chart.

This module states that the presentation form of Stacks Project
[Lemma 70.15.1, Tag 07VS](https://stacks.math.columbia.edu/tag/07VS) implies
the published statement of that lemma for the Library's algebraic spaces. It
imports `Langlands.AlgebraicGeometry.EtaleEquivalenceRelationAffineDescentStatement`
and the published
`Langlands.AlgebraicGeometry.AlgebraicSpace.FiniteSurjectiveAffineDescentStatement`
unchanged. The module states the proposition and supplies no proof.

## Formula

The declaration is
`Langlands.AlgebraicGeometry.EtaleEquivalenceRelationAffineDescentTransferStatement.{u}`.
Its defining formula is

```lean
def EtaleEquivalenceRelationAffineDescentTransferStatement : Prop :=
  EtaleEquivalenceRelationAffineDescentStatement.{u} →
    AlgebraicSpace.FiniteSurjectiveAffineDescentStatement.{u}
```

Both sides use the same arbitrary universe `u`. The hypothesis is the
statement for all étale equivalence relations on affine schemes in
`Scheme.{u}`. The conclusion is the published statement for every base
scheme `S : Scheme.{u}`, every finite surjective morphism `f : X ⟶ Y` of
algebraic spaces over `S` (fppf sheaves on `Over S` with values in
`Type (u + 1)`), with `X` represented by an affine scheme; it concludes that
`Y` is represented by an affine scheme.

There are no parameters or hypotheses outside the implication. Its hypothesis
is exactly

```lean
∀ E : EtaleEquivalenceRelation.{u}, IsAffine E.U →
  E.HasFiniteSurjectiveCoverWithAffineQuotient → E.HasAffineQuotient
```

The cover existentially quantifies another relation `E'` and a cartesian
morphism of relations whose component `E'.U ⟶ E.U` is finite and surjective,
with `E'.HasAffineQuotient`. The conclusion universally quantifies every
`S : Scheme.{u}`, `X Y : AlgebraicSpace S` and `f : X ⟶ Y`, asserting
that the published `IsFinite (hom f)`, `IsSurjective (hom f)` and
`IsRepresentedByAffineScheme X` imply `IsRepresentedByAffineScheme Y`.
The affine representation is absolute, through a natural isomorphism of
presheaves from the functor of points of an affine scheme over `S`.
No further restriction on the relation, its arrows, the cover, the base
or either algebraic space appears in the formula.

## Provenance

This is a derived internal reduction statement for the planned presentation
route to Stacks Lemma 70.15.1,
`FiniteSurjectiveAffineDescentStatement`. It is not stated in this form in the
literature. It records the passage between algebraic spaces and their
presentations, which Stacks uses implicitly. The sources are:

- `stacks-algebraic-space-affine-descent-2026-11-01` (directory SHA-256
  `10fa51455958afc737851009364630c6f8e05ff49d790473a03fa1baaa4c00a0`),
  `07VQ.html`: Lemma 70.15.1 and the first paragraph of its proof (view the
  morphism over `Spec ℤ`; the target is quasi-compact and separated).
- `stacks-etale-equivalence-relations-2026-11-01` (directory SHA-256
  `df1ecbfa63c5e31cf736d9ea79dd262976c3098fd9b36f2dd32668d44bf75420`):
  `0263.html` ([Definition 65.9.3](https://stacks.math.columbia.edu/tag/0263),
  presentations: `R = U ×_Y U` for an étale surjection `U → Y`),
  `02WW.html` ([Theorem 65.10.5](https://stacks.math.columbia.edu/tag/02WW),
  the fppf quotient of an étale equivalence relation is an algebraic space),
  `03C5.html` ([Lemma 39.20.3](https://stacks.math.columbia.edu/tag/03C5),
  the represented quotient criterion) and `07S3.html`
  ([Lemma 39.20.7](https://stacks.math.columbia.edu/tag/07S3),
  cartesian quotient squares).
- `stacks-noetherian-space-affine-descent-2026-11-01` (directory SHA-256
  `6a433fc04ce2561e2cd3cf5f19526887b8fe5ba9b2db5201025e80104df2e6b1`),
  `07VP.html` ([Lemma 69.17.3](https://stacks.math.columbia.edu/tag/07VP)):
  the Noetherian case used at the end of the proof of 07VS, providing context
  for the planned route. Also `03E2.html`, Section 66.5
  ([Definition 66.5.1](https://stacks.math.columbia.edu/tag/03E3)):
  a quasi-compact algebraic space has an étale surjection from a
  quasi-compact scheme. Neither source adds a hypothesis to the formula.

The cited originals and their retained comments were read. Comment #1792
on Section 70.15 concerns Proposition 70.15.2; comment #216 on Theorem
65.10.5 corrects a typo. The other cited tag pages have no comments.
No source-specific errata note was present in the checked workspace,
project or Library errata locations.

The intended argument, which this module does not formalize, runs as
follows. The first paragraph of the proof of 07VS deduces that `Y` is
quasi-compact. By Definition 66.5.1 it therefore has an étale surjection
`V → Y` with `V` a quasi-compact scheme. Choose a finite affine open cover of
`V`; its disjoint union `U` is affine, and `U → V → Y` is étale and
surjective. Then `R = U ×_Y U` with its two
projections is an étale equivalence relation on `U`; its pair of projections
is a monomorphism into the absolute product `U × U`. The base change
`U' = X ×_Y U` with `R' = U' ×_X U'` presents `X`, and the induced morphism of
relations is cartesian with finite surjective component `U' → U`. Since `X`
is affine, the presentation of `X` has an affine quotient. The hypothesis then
gives an affine quotient `M` of the presentation of `Y`, and fppf descent
along `U → M` (Lemma 39.20.3) identifies the quotient with `M`. The structure
map to `S` must also descend to give representation over `S`. The future
proof must implement these comparisons with the Library's actual sheaves,
morphisms and representability predicates.

## Scope and role

This is the transfer step `T` of the planned presentation route. Together
with `EtaleEquivalenceRelationNoetherianApproximationStatement` and a proof of
`NoetherianEtaleEquivalenceRelationAffineDescentStatement`, it gives the
published Lemma 70.15.1 statement. The proof is a separate unit.
All imported Library Lean/Markdown pairs remain unchanged.

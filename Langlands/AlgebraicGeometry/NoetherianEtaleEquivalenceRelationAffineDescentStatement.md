# Noetherian finite-surjective descent of affineness for étale equivalence relations

Authors: Worker 239, Worker 266.

This module states Stacks Project
[Lemma 69.17.3, Tag 07VP](https://stacks.math.columbia.edu/tag/07VP) in the
language of presentations of algebraic spaces by étale equivalence relations.
It is `EtaleEquivalenceRelationAffineDescentStatement` with the extra
hypothesis that the affine scheme `E.U` is Noetherian. It uses the definitions
of `Langlands.AlgebraicGeometry.EtaleEquivalenceRelation` unchanged, and the
Mathlib class `AlgebraicGeometry.IsNoetherian` from
`Mathlib.AlgebraicGeometry.Noetherian`. The module states the proposition and
supplies no proof.

## Formula and quantifiers

The declaration is
`Langlands.AlgebraicGeometry.NoetherianEtaleEquivalenceRelationAffineDescentStatement.{u}`.
Its defining formula is

```lean
def NoetherianEtaleEquivalenceRelationAffineDescentStatement : Prop :=
  ∀ E : EtaleEquivalenceRelation.{u}, IsAffine E.U → IsNoetherian E.U →
    E.HasFiniteSurjectiveCoverWithAffineQuotient → E.HasAffineQuotient
```

The universe `u` is arbitrary, and the quantifier ranges over every étale
equivalence relation `E` with schemes in `Scheme.{u}`, absolute over
`Spec ℤ`. `IsNoetherian E.U` is Mathlib's Noetherian scheme: locally
Noetherian and quasi-compact (class `AlgebraicGeometry.IsNoetherian` in
`Mathlib/AlgebraicGeometry/Noetherian.lean`, pinned Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`). For the affine `E.U` this says
that its ring of global sections is Noetherian. The other hypotheses and the
conclusion are those of `EtaleEquivalenceRelationAffineDescentStatement`;
its Markdown describes them.

## Original source and correspondence

The statement is derived: it is not stated in this form in the literature.
The sources are:

- `stacks-noetherian-space-affine-descent-2026-11-01` (directory SHA-256
  `6a433fc04ce2561e2cd3cf5f19526887b8fe5ba9b2db5201025e80104df2e6b1`):
  `07VP.html` (Lemma 69.17.3: a finite surjective morphism from an affine
  algebraic space to a Noetherian algebraic space has affine target),
  `03EA.html` (Definition 66.24.1: Noetherian means quasi-compact,
  quasi-separated and locally Noetherian), `03E9.html` (Section 66.24,
  Noetherian spaces, with comments #11687 and #11688), `03E2.html`
  (Definition 66.5.1: quasi-compact means that there is a surjective étale
  morphism from a quasi-compact scheme), `03E5.html` (Lemma 66.7.1,
  Definition 66.7.2 and Remark 66.7.3: "locally Noetherian" is étale local
  and may be tested on one surjective étale chart) and `05Z2.html`
  (Lemma 67.9.8: the target of a surjective universally closed morphism from
  a separated space is separated).
- `stacks-algebraic-space-affine-descent-2026-11-01` (directory SHA-256
  `10fa51455958afc737851009364630c6f8e05ff49d790473a03fa1baaa4c00a0`),
  `07VQ.html`: the first paragraph of the proof of Lemma 70.15.1, which
  notes that a finite morphism is affine and universally closed (Morphisms
  of Spaces, Lemma 67.45.7) and applies Lemma 67.9.8.
- `stacks-etale-equivalence-relations-2026-11-01` (directory SHA-256
  `df1ecbfa63c5e31cf736d9ea79dd262976c3098fd9b36f2dd32668d44bf75420`):
  `02WW.html`, `03C5.html` and `07S3.html`, used as in the Markdown of
  `EtaleEquivalenceRelationAffineDescentStatement`.

The correspondence, which this module does not formalize, is that of the
general statement: `Y = E.U/E.R` is an algebraic space, `X = E'.U/E'.R` is
affine, `X → Y` is finite and surjective, and `E.HasAffineQuotient` says that
`Y` is affine. In addition, `Y` is Noetherian in the sense of
Definition 66.24.1:

- `Y` is quasi-compact by Definition 66.5.1 (`03E2`), since `E.U → Y` is
  étale and surjective and `E.U` is quasi-compact.
- `Y` is locally Noetherian by Lemma 66.7.1 and Definition 66.7.2 (`03E5`),
  since the scheme `E.U` of that étale surjection is Noetherian, hence
  locally Noetherian.
- `Y` is separated, hence quasi-separated. As in the first paragraph of the
  proof of Lemma 70.15.1 (`07VQ`), the finite morphism `X → Y` is affine and
  universally closed, it is surjective and `X` is affine, so Lemma 67.9.8
  (`05Z2`) applies.

Lemma 69.17.3 therefore yields this statement. Conversely, every Noetherian
algebraic space `Y` has a presentation with `E.U` Noetherian and affine. As
in the general statement, `Y` has a surjective étale morphism from an affine
scheme `U`. By Lemma 66.7.1, `U` is locally Noetherian, and it is
quasi-compact, so it is Noetherian. Comments #11687 and #11688 on `03E9`
record the same fact. So this statement is Lemma 69.17.3 for presentations.
The published Library statement
`Langlands.AlgebraicGeometry.AlgebraicSpace.NoetherianFiniteSurjectiveAffineDescentStatement`
records the same lemma for the Library's algebraic spaces.

## Scope and role

This statement is the Noetherian case `G_N` of the planned presentation
route to `FiniteSurjectiveAffineDescentStatement`. The statement
`EtaleEquivalenceRelationNoetherianApproximationStatement` says that this
case implies the general `EtaleEquivalenceRelationAffineDescentStatement`.
Proofs are separate units.

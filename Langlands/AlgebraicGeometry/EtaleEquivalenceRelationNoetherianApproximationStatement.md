# Reduction of finite-surjective affine descent to the Noetherian case

Authors: Worker 239 and Worker 148. Worker 239 supplied the shared Lean and
Markdown draft; Worker 148 checked the sources and clarified the quantifiers
and provenance.

This module states the Noetherian-approximation step of the proof of Stacks
Project [Lemma 70.15.1, Tag 07VS](https://stacks.math.columbia.edu/tag/07VS)
in the language of presentations: the Noetherian case implies the general
case. It imports
`Langlands.AlgebraicGeometry.EtaleEquivalenceRelationAffineDescentStatement`
and `Langlands.AlgebraicGeometry.NoetherianEtaleEquivalenceRelationAffineDescentStatement`
unchanged. The module states the proposition and supplies no proof.

## Formula

The declaration is
`Langlands.AlgebraicGeometry.EtaleEquivalenceRelationNoetherianApproximationStatement.{u}`.
Its defining formula is

```lean
def EtaleEquivalenceRelationNoetherianApproximationStatement : Prop :=
  NoetherianEtaleEquivalenceRelationAffineDescentStatement.{u} →
    EtaleEquivalenceRelationAffineDescentStatement.{u}
```

Both sides use the same arbitrary universe `u`. The hypothesis is descent of
affineness for étale equivalence relations on Noetherian affine schemes; the
conclusion is the same descent for étale equivalence relations on all affine
schemes. The Markdown of the two imported modules describes their formulas.

More explicitly, the antecedent is

```lean
∀ E : EtaleEquivalenceRelation.{u}, IsAffine E.U → IsNoetherian E.U →
  E.HasFiniteSurjectiveCoverWithAffineQuotient → E.HasAffineQuotient
```

and the consequent is

```lean
∀ E : EtaleEquivalenceRelation.{u}, IsAffine E.U →
  E.HasFiniteSurjectiveCoverWithAffineQuotient → E.HasAffineQuotient
```

Thus the consequent drops exactly the Noetherian hypothesis on `E.U`.
`IsAffine` and `IsNoetherian` are Mathlib's scheme predicates;
`IsNoetherian` means locally Noetherian and quasi-compact. The cover
existentially quantifies `E'` and a cartesian morphism of relations whose
component `E'.U ⟶ E.U` is finite and surjective, with `E'.HasAffineQuotient`.
The conclusion `E.HasAffineQuotient` asks for an affine scheme `M` and a
flat, locally finitely presented, surjective `q : E.U ⟶ M` whose kernel pair
is `E.R`. All these predicates are the unchanged imported definitions.
There are no parameters or hypotheses outside the implication, and no
additional restriction on `E.R`, the relation arrows or the cover. The
relations are absolute over `Spec ℤ`, so this implication has no base-scheme
or algebraic-space parameter.

## Provenance

This is a derived internal reduction statement for the planned presentation
route to Stacks Lemma 70.15.1,
`FiniteSurjectiveAffineDescentStatement`. It is not stated in this form in the
literature. It records the content of the second and third paragraphs of
Stacks' proof of Lemma 70.15.1 in source
`stacks-algebraic-space-affine-descent-2026-11-01` (directory SHA-256
`10fa51455958afc737851009364630c6f8e05ff49d790473a03fa1baaa4c00a0`),
`07VQ.html`. There the general case is reduced to Lemma 69.17.3 (the
Noetherian case) by writing the target as a directed limit of algebraic
spaces of finite presentation over `Spec ℤ` (absolute Noetherian
approximation, Stacks Proposition 70.8.1), descending the finite surjective
morphism to a finite level, and using that the affineness of a limit is
reached at a finite level (Stacks Lemma 70.5.10).

In detail, the second paragraph first approximates the finite morphism by
finite morphisms of finite presentation (Lemma 70.11.3), reaching an affine
source by Lemma 70.5.10. The third paragraph uses Proposition 70.8.1 to
approximate the target, Lemma 70.7.1 to descend the morphism, and Lemmas
70.6.7, 70.6.4 and 70.5.10 to reach finiteness, surjectivity and an affine
source at a finite level. It then applies the Noetherian case.

The other registered original sources are:

- `stacks-noetherian-space-affine-descent-2026-11-01`, directory SHA-256
  `6a433fc04ce2561e2cd3cf5f19526887b8fe5ba9b2db5201025e80104df2e6b1`,
  `07VP.html`: [Lemma 69.17.3](https://stacks.math.columbia.edu/tag/07VP),
  finite-surjective descent of affineness with Noetherian target.
- `stacks-etale-equivalence-relations-2026-11-01`, directory SHA-256
  `df1ecbfa63c5e31cf736d9ea79dd262976c3098fd9b36f2dd32668d44bf75420`:
  `0263.html`, [Definition 65.9.3](https://stacks.math.columbia.edu/tag/0263)
  (presentations); `02WW.html`,
  [Theorem 65.10.5](https://stacks.math.columbia.edu/tag/02WW) (algebraic
  space quotients); `03C5.html`,
  [Lemma 39.20.3](https://stacks.math.columbia.edu/tag/03C5) (represented
  quotient criterion); and `07S3.html`,
  [Lemma 39.20.7](https://stacks.math.columbia.edu/tag/07S3) (cartesian
  quotient squares). These explain the presentation vocabulary on both
  sides of the implication.

The cited originals and their retained comments were read. Comment #1792
on Section 70.15 concerns Proposition 70.15.2; comment #216 on Theorem
65.10.5 corrects a typo. The other cited tag pages have no comments.
No source-specific errata note was present in the checked workspace,
project or Library errata locations.

The future proof must construct and compare suitable Noetherian finite-level
presentations and affine quotients. This declaration supplies no approximation
data or limit theorem, and assumes no such result as an extra hypothesis.
The numbered limit results above are cited as steps explicitly invoked in
the retained proof of 07VS; this module does not formalize their individual
statements.

## Scope and role

This is the approximation step of the planned presentation route. Together
with `EtaleEquivalenceRelationAffineDescentTransferStatement` and a proof of
`NoetherianEtaleEquivalenceRelationAffineDescentStatement`, it gives the
published Lemma 70.15.1 statement. The proof is a separate unit.
All imported Library Lean/Markdown pairs remain unchanged.

# Finite-surjective descent of affineness for étale equivalence relations

Authors: Worker 239, Worker 266.

This module states Stacks Project
[Lemma 70.15.1, Tag 07VS](https://stacks.math.columbia.edu/tag/07VS) in the
language of presentations of algebraic spaces by étale equivalence relations.
It uses the definitions of `Langlands.AlgebraicGeometry.EtaleEquivalenceRelation`
unchanged. The module states the proposition and supplies no proof.

## Formula and quantifiers

The declaration is
`Langlands.AlgebraicGeometry.EtaleEquivalenceRelationAffineDescentStatement.{u}`.
Its defining formula is

```lean
def EtaleEquivalenceRelationAffineDescentStatement : Prop :=
  ∀ E : EtaleEquivalenceRelation.{u}, IsAffine E.U →
    E.HasFiniteSurjectiveCoverWithAffineQuotient → E.HasAffineQuotient
```

The universe `u` is arbitrary. The quantifier ranges over every étale
equivalence relation `E` whose schemes `E.U` and `E.R` lie in `Scheme.{u}`.
Everything is absolute, over `Spec ℤ`, as explained in the Markdown of the
definitions module.

- `IsAffine E.U` is Mathlib's absolute affineness of the scheme `E.U`. Nothing
  is assumed about `E.R`.
- `E.HasFiniteSurjectiveCoverWithAffineQuotient` supplies an étale equivalence
  relation `E'`, morphisms `f : E'.U ⟶ E.U` and `g : E'.R ⟶ E.R` with
  `g ≫ E.t = E'.t ≫ f` and `IsPullback g E'.s E.s f`, with `f` finite and
  surjective, and with `E'.HasAffineQuotient`.
- The conclusion `E.HasAffineQuotient` asks for an affine scheme `M` and a
  flat, locally finitely presented, surjective `q : E.U ⟶ M` with
  `IsPullback E.t E.s q q`.

No Noetherian, finite-presentation, quasi-compactness or separatedness
hypothesis is imposed on `E.R`, on the morphisms `E.t` and `E.s`, or on the
cover.

## Original source and correspondence

The statement is derived: it is not stated in this form in the literature.
It restates Lemma 70.15.1 for an algebraic space presented by an étale
equivalence relation on an affine scheme. The sources are:

- `stacks-algebraic-space-affine-descent-2026-11-01` (directory SHA-256
  `10fa51455958afc737851009364630c6f8e05ff49d790473a03fa1baaa4c00a0`),
  `07VQ.html`: Lemma 70.15.1. If `f : X → Y` is a finite surjective morphism
  of algebraic spaces and `X` is affine, then `Y` is affine.
- `stacks-etale-equivalence-relations-2026-11-01` (directory SHA-256
  `df1ecbfa63c5e31cf736d9ea79dd262976c3098fd9b36f2dd32668d44bf75420`):
  `02WW.html` (Theorem 65.10.5: `U/R` is an algebraic space with
  `U → U/R` étale and surjective), `03C5.html` (Lemma 39.20.3: an fppf
  `q : U → M` with `R ≅ U ×_M U` makes `M` represent `U/R`) and `07S3.html`
  (Lemma 39.20.7: for a morphism of equivalence relations whose `s`-square is
  cartesian, `U' = U ×_{U/R} U'/R'`).
- `stacks-noetherian-space-affine-descent-2026-11-01` (directory SHA-256
  `6a433fc04ce2561e2cd3cf5f19526887b8fe5ba9b2db5201025e80104df2e6b1`),
  `03E2.html`: Definition 66.5.1. An algebraic space is quasi-compact if it
  has a surjective étale morphism from a quasi-compact scheme.

The correspondence, which this module does not formalize, is as follows. Put
`Y = E.U/E.R` and `X = E'.U/E'.R`. By `03C5`, `E'.HasAffineQuotient` makes
`X` an affine scheme. By `07S3`, `E'.U` is the base change of `X → Y` along
the étale surjection `E.U → Y`, so `X → Y` is finite and surjective because
`f` is. Conversely, if `Y` is an affine scheme, then `E.U → Y` is étale and
surjective, hence flat, locally of finite presentation and surjective, and
`E.R = E.U ×_Y E.U`; this gives `E.HasAffineQuotient`. By `03C5` again,
`E.HasAffineQuotient` says that `Y` is affine. Lemma 70.15.1 for `X → Y`
therefore yields this statement.

Stacks proves Lemma 70.15.1 over an arbitrary base and first views
everything over `Spec ℤ` (first sentence of its proof). The absolute setting
here is that viewpoint. The hypothesis `IsAffine E.U` makes `Y`
quasi-compact by Definition 66.5.1 (`03E2`), since `E.U → Y` is étale and
surjective. Conversely, in Lemma 70.15.1 the target is quasi-compact because
the affine source maps onto it (first paragraph of its proof). By
Definition 66.5.1 the target then has a surjective étale morphism from a
quasi-compact scheme. The disjoint union of finitely many affine opens
covering that scheme is an affine scheme with a surjective étale morphism to
the target. So every target of that lemma has a presentation with `E.U`
affine.

## Scope and role

This statement is the general case `G` of the planned presentation route to
`FiniteSurjectiveAffineDescentStatement`. The companion statements are
`NoetherianEtaleEquivalenceRelationAffineDescentStatement` (the Noetherian
case), `EtaleEquivalenceRelationAffineDescentTransferStatement` (this
statement implies the published Lemma 70.15.1 statement) and
`EtaleEquivalenceRelationNoetherianApproximationStatement` (the Noetherian
case implies this statement). Proofs are separate units.

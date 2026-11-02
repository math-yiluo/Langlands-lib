# A Noetherian level carrying the finite surjective cover

Authors: Worker 239 and Worker 1224. Worker 239 supplied the shared Lean and
Markdown draft; Worker 1224 checked it against the cited sources and refined
the correspondence.

This module states, in the language of presentations of algebraic spaces by
étale equivalence relations, the middle step of the proof of Stacks Project
[Lemma 70.15.1, Tag 07VS](https://stacks.math.columbia.edu/tag/07VS): once an
algebraic space is affine over a Noetherian algebraic space, its finite
surjective cover by an affine space descends to a Noetherian level. It uses
the definitions of `Langlands.AlgebraicGeometry.EtaleEquivalenceRelation`
unchanged (`EtaleEquivalenceRelation`, `EtaleEquivalenceRelation.IsCartesianHom`,
`EtaleEquivalenceRelation.HasFiniteSurjectiveCoverWithAffineQuotient`), and
the Mathlib classes `AlgebraicGeometry.IsAffine` and
`AlgebraicGeometry.IsNoetherian`. The module states the proposition and
supplies no proof.

## Formula and quantifiers

The declaration is
`Langlands.AlgebraicGeometry.EtaleEquivalenceRelationNoetherianCoverLevelStatement.{u}`.
Its defining formula is

```lean
def EtaleEquivalenceRelationNoetherianCoverLevelStatement : Prop :=
  ∀ (E E₀ : EtaleEquivalenceRelation.{u}) (f : E.U ⟶ E₀.U) (g : E.R ⟶ E₀.R),
    EtaleEquivalenceRelation.IsCartesianHom E E₀ f g → IsAffine E.U → IsAffine E₀.U →
      IsNoetherian E₀.U → IsAffine E₀.R → E.HasFiniteSurjectiveCoverWithAffineQuotient →
        ∃ (E₁ : EtaleEquivalenceRelation.{u}) (f₁ : E.U ⟶ E₁.U) (g₁ : E.R ⟶ E₁.R),
          EtaleEquivalenceRelation.IsCartesianHom E E₁ f₁ g₁ ∧ IsAffine E₁.U ∧
            IsNoetherian E₁.U ∧ E₁.HasFiniteSurjectiveCoverWithAffineQuotient
```

The universe `u` is arbitrary. The quantifiers range over all étale
equivalence relations `E` and `E₀` with schemes in `Scheme.{u}`, absolute
over `Spec ℤ`, and all morphisms `f : E.U ⟶ E₀.U` and `g : E.R ⟶ E₀.R`. The
hypotheses are:

- `IsCartesianHom E E₀ f g`: `g ≫ E₀.t = E.t ≫ f`, and the square formed by
  `g`, `E.s`, `E₀.s` and `f` is a pullback (Stacks Tag 0APD);
- `E.U` is affine; `E₀.U` is affine and Noetherian (Mathlib's
  `IsNoetherian`: locally Noetherian and quasi-compact); `E₀.R` is affine;
- `E.HasFiniteSurjectiveCoverWithAffineQuotient`: there are an étale
  equivalence relation `E'` with an affine quotient and a cartesian morphism
  `E' ⟶ E` whose component on the underlying schemes is finite and
  surjective.

The conclusion gives an étale equivalence relation `E₁` in the same universe
and a cartesian morphism `(f₁, g₁) : E ⟶ E₁` such that `E₁.U` is affine and
Noetherian and `E₁` has a finite surjective cartesian cover by an étale
equivalence relation with an affine quotient. It does not say that `E₁.R` is
affine, and it does not relate `E₁` to `E₀`.

## Original source and correspondence

The statement is derived: it is not stated in this form in the literature.
It extracts the second and third paragraphs of the proof of Lemma 70.15.1,
up to the point where the Noetherian case is applied, for an algebraic space
that is affine over a Noetherian one. The sources are:

- `stacks-algebraic-space-affine-descent-2026-11-01` (directory SHA-256
  `10fa51455958afc737851009364630c6f8e05ff49d790473a03fa1baaa4c00a0`),
  `07VQ.html`: Lemma 70.15.1 and its proof. The first paragraph shows that
  the target `Y` of a finite surjective morphism from an affine space is
  separated and quasi-compact. The second reduces to a cover of finite
  presentation by Lemmas 70.11.3 and 70.5.10. The third writes `Y` as a
  limit, descends the cover to a level, and makes it finite, surjective and
  affine there by Lemmas 70.7.1, 70.6.7, 70.6.4 and 70.5.10.
- `stacks-noetherian-approximation-2026-11-01` (directory SHA-256
  `a9a500a6ecf5ab8155bccd57e5fff0616f581d41e9256563c7821a5b81019625`):
  `0870.html` (Lemma 70.11.1: an affine morphism to a quasi-compact and
  quasi-separated space is a directed limit of affine morphisms of finite
  presentation), `07VR.html` (Lemma 70.11.3), `07SF.html` (Lemma 70.4.1),
  `084R.html` (Situation 70.5.5), `084W.html` (Situation 70.6.1),
  `07SK.html` (Lemma 70.7.1), `084Z.html` (Lemma 70.6.7: finiteness
  descends), `07SN.html` (Lemma 70.6.4: surjectivity descends) and
  `07SQ.html` (Lemma 70.5.10: if the limit is affine, then some level is
  affine). The proof of Proposition 70.8.1 in `07SU.html` cites Morphisms of
  Spaces, Lemma 67.20.3, for the fact that a morphism of spaces is affine
  when its base change along a surjective étale morphism from a scheme is
  affine.
- `stacks-etale-equivalence-relations-2026-11-01` (directory SHA-256
  `df1ecbfa63c5e31cf736d9ea79dd262976c3098fd9b36f2dd32668d44bf75420`):
  `02WW.html` (Theorem 65.10.5), `0263.html` (Definition 65.9.3:
  presentations), `03C5.html` (Lemma 39.20.3: affine quotients), `07S3.html`
  (Lemma 39.20.7: for a cartesian morphism of equivalence relations,
  `U' = U ×_{U/R} U'/R'`) and `0APD.html` (cartesian morphisms).
- `stacks-noetherian-space-affine-descent-2026-11-01` (directory SHA-256
  `6a433fc04ce2561e2cd3cf5f19526887b8fe5ba9b2db5201025e80104df2e6b1`):
  `03EA.html` (Definition 66.24.1: Noetherian means quasi-compact,
  quasi-separated and locally Noetherian), `03E2.html` (Definition 66.5.1:
  quasi-compact) and `03E5.html` (Lemma 66.7.1 and Definition 66.7.2:
  "locally Noetherian" is étale local and may be tested on one surjective
  étale chart).
- `stacks-serre-criterion-algebraic-spaces-2026-11-01` (directory SHA-256
  `87667c307924301da4b8d890a4cd77f1dbee3773a5130a698624e661014c8e5e`),
  `02X4.html`: the proof of Lemma 65.13.1 shows that the square formed by `j`
  and the diagonal is cartesian, so the diagonal is quasi-compact when `j`
  is.
- `stacks-algebraic-spaces-foundations-2026-11-01` (directory SHA-256
  `398dc48cec8605ced66045042e97948174a3ec96d41edb157b703103a6b04be9`),
  `025Y.html` (Definition 65.6.1: the diagonal of an algebraic space is
  representable).

The correspondence, which this module does not formalize, is as follows. Put
`Y = E.U/E.R` and `Y₀ = E₀.U/E₀.R` (`02WW`). By `07S3` the cartesian
morphism `(f, g)` induces `Y → Y₀` with `E.U = E₀.U ×_{Y₀} Y`. The morphism
`f` of affine schemes is affine, so `Y → Y₀` is affine (Morphisms of Spaces,
Lemma 67.20.3, as cited in `07SU`). `Y₀` is Noetherian (`03EA`): it is
quasi-compact (`03E2`) and locally Noetherian (`03E5`), and it is
quasi-separated (`02X4`) because `j₀ : E₀.R → E₀.U × E₀.U` is a morphism of
affine schemes, hence quasi-compact. As in the Markdown of
`EtaleEquivalenceRelationAffineDescentStatement`, the cover gives an affine
scheme `X = E'.U/E'.R` (`03C5`) with a finite surjective morphism `X → Y`
(`07S3`). By the first paragraph of `07VQ`, `Y` is separated and
quasi-compact.

As in the second paragraph of `07VQ`, Lemma 70.11.3 writes `X = lim X_a`
with closed immersions as transition maps and `X_a → Y` finite and of finite
presentation, and Lemma 70.5.10 makes some `X_a` affine. Then `X ⊂ X_a` is
closed and `X_a → Y` is surjective, so we may assume that `X → Y` is also of
finite presentation. By Lemma 70.11.1, applied to the affine morphism
`Y → Y₀`, `Y = lim Y_j` with each `Y_j` affine and of finite presentation
over `Y₀`; the transition morphisms are affine, being morphisms of spaces
affine over `Y₀`. Each `Y_j` is Noetherian (`03EA`): it is quasi-compact and
quasi-separated, being affine over `Y₀`, and its surjective étale chart
`E₀.U ×_{Y₀} Y_j` is affine and of finite type over the Noetherian `E₀.U`,
hence a Noetherian scheme, so `Y_j` is locally Noetherian (`03E5`). In
particular Situation 70.5.5 applies to the system `(Y_j)`. As in the third paragraph of `07VQ`, Lemma 70.7.1 gives a morphism
`X_j → Y_j` of finite presentation with base change `X → Y`. Increasing `j`,
it is finite (Lemma 70.6.7), surjective (Lemma 70.6.4) and `X_j` is affine
(Lemma 70.5.10 for the system `X_j ×_{Y_j} Y_{j'}`, whose limit is `X` by
Lemma 70.4.1).

Fix such a `j`. Put `E₁.U = E₀.U ×_{Y₀} Y_j`, an affine Noetherian scheme,
and `E₁.R = E₁.U ×_{Y_j} E₁.U`, a scheme (`025Y`). This is a presentation of
`Y_j` (`0263`). Since `E.U = E₁.U ×_{Y_j} Y`, the cartesian morphism
`(f₁, g₁) : E ⟶ E₁` arises exactly as in the Markdown of
`EtaleEquivalenceRelationNoetherianFirstLevelStatement`. Put
`E₁'.U = X_j ×_{Y_j} E₁.U`, a scheme finite and surjective over `E₁.U` as a
base change of `X_j → Y_j`, and `E₁'.R = E₁'.U ×_{X_j} E₁'.U`. Then `E₁'` is
an étale equivalence relation presenting `X_j`. The projections give a
cartesian morphism `E₁' ⟶ E₁`, because
`E₁'.R = E₁.R ×_{s, E₁.U} E₁'.U`. Since `X_j` is affine, `E₁'.U → X_j` is
flat, locally of finite presentation and surjective with
`E₁'.R = E₁'.U ×_{X_j} E₁'.U`, so `E₁'` has an affine quotient. Hence `E₁`
has the required cover.

## Scope and role

This statement is the second of three steps in the planned proof of
`EtaleEquivalenceRelationNoetherianApproximationStatement`. It is applied to
the first level `E₀` given by
`EtaleEquivalenceRelationNoetherianFirstLevelStatement`. The Noetherian case
`NoetherianEtaleEquivalenceRelationAffineDescentStatement` then makes the
quotient of `E₁` affine, and
`EtaleEquivalenceRelationCartesianAffineQuotientStatement` pulls this back to
`E`.

The proof is a separate unit, and the route above is one option. In ring
terms, `Γ(E.U)` is a `Γ(E₀.U)`-algebra with a coaction of `Γ(E₀.R)`, and
the levels `Y_j` correspond to finitely generated subalgebras stable under
the coaction. Such subalgebras exhaust `Γ(E.U)` by Groupoid Schemes,
Lemmas 39.15.1, 39.15.3 and 39.15.4 (`07TR`, `07TT`, `07TU`, in the second
source). Here `E₀.R` is Noetherian, being affine and étale over the
Noetherian `E₀.U`. The finite cover can be descended in the same way.

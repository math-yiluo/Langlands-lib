# A Noetherian first level for separated étale equivalence relations

Authors: Worker 239 and Worker 1224. Worker 239 supplied the shared Lean and
Markdown draft; Worker 1224 checked it against the cited sources and refined
the correspondence.

This module states, in the language of presentations of algebraic spaces by
étale equivalence relations, the first level of absolute Noetherian
approximation (Stacks Project
[Proposition 70.8.1, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)) for
separated quasi-compact algebraic spaces. It uses the definitions of
`Langlands.AlgebraicGeometry.EtaleEquivalenceRelation` unchanged
(`EtaleEquivalenceRelation`, `EtaleEquivalenceRelation.IsCartesianHom`), and
the Mathlib notions `AlgebraicGeometry.IsAffine`,
`AlgebraicGeometry.IsClosedImmersion`, `AlgebraicGeometry.IsNoetherian` and
`CategoryTheory.Limits.prod.lift`. The module states the proposition and
supplies no proof.

## Formula and quantifiers

The declaration is
`Langlands.AlgebraicGeometry.EtaleEquivalenceRelationNoetherianFirstLevelStatement.{u}`.
Its defining formula is

```lean
def EtaleEquivalenceRelationNoetherianFirstLevelStatement : Prop :=
  ∀ E : EtaleEquivalenceRelation.{u}, IsAffine E.U →
    IsClosedImmersion (prod.lift E.t E.s) →
      ∃ (E₀ : EtaleEquivalenceRelation.{u}) (f : E.U ⟶ E₀.U) (g : E.R ⟶ E₀.R),
        EtaleEquivalenceRelation.IsCartesianHom E E₀ f g ∧ IsAffine E₀.U ∧
          IsNoetherian E₀.U ∧ IsAffine E₀.R
```

The universe `u` is arbitrary. The quantifier ranges over every étale
equivalence relation `E` with schemes in `Scheme.{u}`, absolute over
`Spec ℤ`. There are two hypotheses:

- `IsAffine E.U`: the scheme `E.U` is affine.
- `IsClosedImmersion (prod.lift E.t E.s)`: the morphism
  `j = (t, s) : E.R ⟶ E.U ⨯ E.U` into the categorical product of schemes
  (the product over `Spec ℤ`) is a closed immersion.

The hypotheses imply that `E.R` is affine, as a closed subscheme of the
affine scheme `E.U ⨯ E.U`; the formula does not state this.

The conclusion gives an étale equivalence relation `E₀` in the same universe
and morphisms `f : E.U ⟶ E₀.U` and `g : E.R ⟶ E₀.R` such that:

- `IsCartesianHom E E₀ f g`: `g ≫ E₀.t = E.t ≫ f`, and the square formed by
  `g`, `E.s`, `E₀.s` and `f` is a pullback (Stacks Tag 0APD);
- `E₀.U` is affine and Noetherian (Mathlib's `IsNoetherian`: locally
  Noetherian and quasi-compact; for the affine `E₀.U` this says that its ring
  of global sections is Noetherian);
- `E₀.R` is affine.

The statement asserts no uniqueness, says nothing about `E₀.U` being of
finite type over `ℤ`, and does not claim that `(E₀.t, E₀.s)` is a closed
immersion.

## Original source and correspondence

The statement is derived: it is not stated in this form in the literature.
It is a consequence of Proposition 70.8.1 and of descent along limits of
algebraic spaces, rewritten for presentations. The sources are:

- `stacks-noetherian-approximation-2026-11-01` (directory SHA-256
  `a9a500a6ecf5ab8155bccd57e5fff0616f581d41e9256563c7821a5b81019625`):
  `07SU.html` (Proposition 70.8.1: a quasi-compact and quasi-separated
  algebraic space over `Spec(Z)` is a directed limit `lim X_i` of
  quasi-separated algebraic spaces of finite type over `Z` with affine
  transition morphisms), `07SF.html` (Lemma 70.4.1: such limits exist, and
  `X ×_{X_i} T = lim_{i' ≥ i} X_{i'} ×_{X_i} T`), `084R.html`
  (Situation 70.5.5), `084W.html` (Situation 70.6.1), `07SK.html`
  (Lemma 70.7.1: spaces of finite presentation over the limit descend to a
  level), `07SL.html` (Lemma 70.6.2: étaleness descends), `07SN.html`
  (Lemma 70.6.4: surjectivity descends), `07SQ.html` (Lemma 70.5.10: if the
  limit is affine, then some level is affine), `07SI.html` (Lemma 70.5.6,
  whose proof notes that the schemes `R_i` of such a system of presentations
  are quasi-compact and separated), `086P.html`
  (Situation 32.4.5) and `01Z6.html` (Lemma 32.4.13: the same for limits of
  quasi-compact and quasi-separated schemes).
- `stacks-etale-equivalence-relations-2026-11-01` (directory SHA-256
  `df1ecbfa63c5e31cf736d9ea79dd262976c3098fd9b36f2dd32668d44bf75420`):
  `02WW.html` (Theorem 65.10.5: `U/R` is an algebraic space with `U → U/R`
  étale and surjective), `0263.html` (Definition 65.9.3: in a presentation,
  `R = U ×_F U`), `07S3.html` (Lemma 39.20.7: for a morphism of equivalence
  relations whose `s`-square is cartesian, `U' = U ×_{U/R} U'/R'`) and
  `0APD.html` (cartesian morphisms of groupoids).
- `stacks-serre-criterion-algebraic-spaces-2026-11-01` (directory SHA-256
  `87667c307924301da4b8d890a4cd77f1dbee3773a5130a698624e661014c8e5e`),
  `02X4.html`: the proof of Lemma 65.13.1 shows that for a presentation
  `F = U/R` the square formed by `j : R → U × U` and the diagonal
  `Δ : F → F × F` is cartesian, with `U × U → F × F` étale and surjective.
  So properties of `Δ` that are local in the fpqc topology, such as being a
  closed immersion or being quasi-compact, can be checked on `j`.
- `stacks-algebraic-spaces-foundations-2026-11-01` (directory SHA-256
  `398dc48cec8605ced66045042e97948174a3ec96d41edb157b703103a6b04be9`),
  `025Y.html`: Definition 65.6.1. An algebraic space is an fppf sheaf with
  representable diagonal and a surjective étale morphism from a scheme.
- `stacks-finite-flat-groupoid-quotient-2026-11-01` (directory SHA-256
  `04098502d60fbca6624b86128e0360936b8a62bff64fa4765db553d0f7466304`),
  `03BS.html`: Definition 66.3.1. An algebraic space is separated if its
  diagonal is a closed immersion.
- `stacks-noetherian-space-affine-descent-2026-11-01` (directory SHA-256
  `6a433fc04ce2561e2cd3cf5f19526887b8fe5ba9b2db5201025e80104df2e6b1`),
  `03E2.html`: Definition 66.5.1. An algebraic space is quasi-compact if it
  has a surjective étale morphism from a quasi-compact scheme.

The correspondence, which this module does not formalize, is as follows.
Put `Y = E.U/E.R`. By `02WW` and `0263`, `Y` is an algebraic space,
`E.U → Y` is étale and surjective, and `E.R = E.U ×_Y E.U` with `j` the
canonical morphism. `Y` is quasi-compact by `03E2`. By `02X4` the diagonal of
`Y` is a closed immersion because `j` is one, so `Y` is separated (`03BS`),
hence quasi-separated.

Proposition 70.8.1 writes `Y = lim Y_i` as in its statement: the `Y_i` are
quasi-separated and of finite type over `ℤ`, hence quasi-compact, and the
transition morphisms are affine. The morphism `E.U → Y` is étale, hence
locally of finite presentation. It is quasi-compact because `E.U` is
quasi-compact and `Y` is quasi-separated, and quasi-separated because the
affine scheme `E.U` is separated; so it is of finite presentation. By
Lemma 70.7.1 there are an index `i` and a morphism `U_i → Y_i` of finite
presentation whose base change to `Y` is `E.U → Y`. Increasing `i`, it is
étale by Lemma 70.6.2 and surjective by Lemma 70.6.4 (Situation 70.6.1 with
`B_i = Y_i`). For `i' ≥ i` put `U_{i'} = U_i ×_{Y_i} Y_{i'}`; the base change
`U_{i'} → Y_{i'}` is again étale and surjective. By Lemma 70.4.1 the system
`(U_{i'})` has affine transition morphisms and limit `E.U`. These spaces are
quasi-compact and quasi-separated, being of finite presentation over
`Y_{i'}`, so Situation 70.5.5 applies. Since `E.U` is affine, Lemma 70.5.10
makes `U_{i'}` affine for large `i'`.

For such `i'` put `R_{i'} = U_{i'} ×_{Y_{i'}} U_{i'}`. It is a scheme
because the diagonal of `Y_{i'}` is representable (`025Y`). Its two
projections are base changes of the étale morphism `U_{i'} → Y_{i'}`, and
`R_{i'} → U_{i'} × U_{i'}` is a monomorphism, being a base change of the
diagonal of `Y_{i'}` (the square of `02X4`), so `(U_{i'}, R_{i'})` is an
étale equivalence relation and `(U_{i'}, R_{i'}, U_{i'} → Y_{i'})` is a
presentation of `Y_{i'}` (`0263`). The scheme `R_{i'}` is quasi-compact
because `Y_{i'}` is quasi-separated (`02X4`). Since
`E.U = U_{i'} ×_{Y_{i'}} Y`, the projection is a morphism `f : E.U → U_{i'}`,
and

`E.R = E.U ×_Y E.U = U_{i'} ×_{Y_{i'}} E.U = R_{i'} ×_{s, U_{i'}, f} E.U`.

This gives `g : E.R → R_{i'}`, commuting with both projections, such that the
square of `s`-projections is cartesian. This is `IsCartesianHom`, the
cartesian morphism of `0APD` (compare `07S3`).

For `i'' ≥ i'` the scheme `R_{i''} = R_{i'} ×_{Y_{i'}} Y_{i''}` is the base
change of `R_{i'}` along the affine morphism `U_{i''} → U_{i'}` (via `s`). By
Lemma 70.4.1 the limit of the `R_{i''}` is `R_{i'} ×_{Y_{i'}} Y = E.R`. These
are quasi-compact and separated schemes, as noted in the proof of
Lemma 70.5.6 (`07SI`) for the same construction, with affine transition
morphisms. So Situation 32.4.5 applies, and since `E.R` is affine,
Lemma 32.4.13 makes `R_{i''}` affine for large `i''`. Finally `U_{i''}` is étale over `Y_{i''}`,
which is of finite type over `ℤ`. So the affine scheme `U_{i''}` is of finite
type over `ℤ`, and it is Noetherian by the Hilbert basis theorem. With
`E₀ = (U_{i''}, R_{i''})` for a large `i''`, the conclusion holds.

## Scope and role

This statement is the first of three steps in the planned proof of
`EtaleEquivalenceRelationNoetherianApproximationStatement` (the Noetherian
case `G_N` implies the general case `G` of finite-surjective descent of
affineness). Let `E` satisfy the hypotheses of `G`. The published
`EtaleEquivalenceRelationAffineRelationStatement` makes `j` a closed
immersion. This statement then gives a Noetherian first level `E₀`.
`EtaleEquivalenceRelationNoetherianCoverLevelStatement` moves the finite
surjective cover to a Noetherian level `E₁`, `G_N` makes the quotient of
`E₁` affine, and `EtaleEquivalenceRelationCartesianAffineQuotientStatement`
pulls this back to `E`.

The proof is a separate unit. Its main work is Proposition 70.8.1 itself in
the language of presentations. That proof (`07SU`) uses the stratification of
Decent Spaces, Lemma 68.8.6 (`07ST`), the absolute approximation of schemes
(Limits, Lemma 32.5.3 and Proposition 32.5.4: `07RN`, `01ZA`) and pushouts of
schemes along open immersions. All of these pages are in the first source.

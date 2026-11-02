# The relation scheme of a finitely covered étale equivalence relation

Authors: Worker 239, Worker 712.

This module states that, under the hypotheses of
`EtaleEquivalenceRelationAffineDescentStatement`, the relation scheme `E.R`
is affine and `j = (t, s) : E.R ⟶ E.U × E.U` is a closed immersion. In the
language of algebraic spaces this is the conclusion that Stacks Project,
Lemma 66.3.4 (Tag 0AHS), draws for `U = V = E.U` from the separatedness of
the quotient `E.U/E.R`; the module does not formalize algebraic spaces or
this correspondence. It uses the definitions of
`Langlands.AlgebraicGeometry.EtaleEquivalenceRelation` unchanged, and the
Mathlib class `AlgebraicGeometry.IsClosedImmersion` from
`Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`. The module states the
proposition and supplies no proof.

## Formula and quantifiers

The declaration is
`Langlands.AlgebraicGeometry.EtaleEquivalenceRelationAffineRelationStatement.{u}`.
Its defining formula is

```lean
def EtaleEquivalenceRelationAffineRelationStatement : Prop :=
  ∀ E : EtaleEquivalenceRelation.{u}, IsAffine E.U →
    E.HasFiniteSurjectiveCoverWithAffineQuotient →
      IsAffine E.R ∧ IsClosedImmersion (prod.lift E.t E.s)
```

The universe `u` is arbitrary. The quantifier ranges over every étale
equivalence relation `E` with schemes in `Scheme.{u}`, absolute over
`Spec ℤ`.

- The hypotheses `IsAffine E.U` and
  `E.HasFiniteSurjectiveCoverWithAffineQuotient` are those of
  `EtaleEquivalenceRelationAffineDescentStatement`; its Markdown describes
  them. Nothing is assumed about `E.R`.
- `IsAffine E.R` is Mathlib's absolute affineness of the scheme `E.R`.
- `prod.lift E.t E.s : E.R ⟶ E.U ⨯ E.U` is the morphism `j = (t, s)` into
  the categorical product of schemes, which is the fibre product over
  `Spec ℤ`. `IsClosedImmersion` is Mathlib's class of closed immersions of
  schemes: a closed embedding of underlying spaces whose induced maps on
  stalks are surjective.

Since `E.U` is affine, so is `E.U ⨯ E.U`, and a closed immersion into an
affine scheme has affine source. The first conjunct therefore follows from
the second. It is stated separately because it is the form used later.

## Original source and correspondence

The statement is derived: it is not stated in this form in the literature.
The sources are:

- `stacks-finite-flat-groupoid-quotient-2026-11-01` (directory SHA-256
  `04098502d60fbca6624b86128e0360936b8a62bff64fa4765db553d0f7466304`):
  `03BS.html` (Definition 66.3.1: an algebraic space over `Spec ℤ` is
  separated if its diagonal is a closed immersion), `0AHS.html`
  (Lemma 66.3.4: `X` is separated if and only if for all morphisms
  `U → X`, `V → X` from affine schemes the fibre product `U ×_X V` is affine
  and `O(U) ⊗_ℤ O(V) → O(U ×_X V)` is surjective), `05Z2.html`
  (Lemma 67.9.8 (2): the target of a surjective universally closed morphism
  from a separated algebraic space is separated), `0414.html`
  (Lemma 67.45.6: finite morphisms are integral), `0415.html`
  (Lemma 67.45.7: integral morphisms are affine and universally closed) and
  `04XV.html` (Étale Morphisms, Lemma 41.7.2: a morphism of schemes is a
  closed immersion if and only if it is universally closed, locally of finite
  type and a monomorphism; used only in the proof sketch under Scope and
  role).
- `stacks-algebraic-space-affine-descent-2026-11-01` (directory SHA-256
  `10fa51455958afc737851009364630c6f8e05ff49d790473a03fa1baaa4c00a0`),
  `07VQ.html`: the first paragraph of the proof of Lemma 70.15.1, which shows
  that the target of a finite surjective morphism from an affine algebraic
  space is separated, using Lemmas 67.45.7 and 67.9.8.
- `stacks-etale-equivalence-relations-2026-11-01` (directory SHA-256
  `df1ecbfa63c5e31cf736d9ea79dd262976c3098fd9b36f2dd32668d44bf75420`):
  `0263.html` (Definition 65.9.3: in a presentation, `R = U ×_F U`),
  `02WW.html`, `03C5.html` and `07S3.html`, used as in the Markdown of
  `EtaleEquivalenceRelationAffineDescentStatement`.

The correspondence, which this module does not formalize, is as follows. Put
`Y = E.U/E.R` and `X = E'.U/E'.R`. As explained in the Markdown of
`EtaleEquivalenceRelationAffineDescentStatement`, `X` is an affine scheme
(`03C5`) and `X → Y` is finite and surjective (`07S3`). As in the first
paragraph of the proof of Lemma 70.15.1 (`07VQ`), `X → Y` is integral
(`0414`), hence universally closed (`0415`), and `X` is separated, so `Y` is
separated by Lemma 67.9.8 (`05Z2`). By Theorem 65.10.5 (`02WW`) and
Definition 65.9.3 (`0263`), `E.U → Y` is part of a presentation, so `E.R` is
`E.U ×_Y E.U` with `j = (t, s)` the canonical morphism to `E.U × E.U`.
Lemma 66.3.4 (`0AHS`) with `U = V = E.U` then says that `E.R` is affine and
that the ring map `O(E.U) ⊗_ℤ O(E.U) → O(E.R)` is surjective. Since
`E.U × E.U` is the affine scheme `Spec(O(E.U) ⊗_ℤ O(E.U))`, this means that
`j` is a closed immersion. This is the statement.

## Scope and role

This statement belongs to the planned proof of the Noetherian case
`NoetherianEtaleEquivalenceRelationAffineDescentStatement`. There both `E.U`
and `E.R` must be affine, so that the relation can be written with rings. The
statement assumes no Noetherian hypothesis and may be proved directly at the
scheme level. For example, `j` is a monomorphism (the field `mono_lift`) and
is locally of finite type because `E.t = j ≫ pr₁` is étale. The morphism
`g : E'.R ⟶ E.R` is surjective, being the base change of the surjection `f`
along `E.s`. The composite `g ≫ j` equals `j' ≫ (f × f)`, where `j'` is the
morphism `(E'.t, E'.s) : E'.R ⟶ E'.U × E'.U`. Here `j'` is a closed
immersion, a base change of the diagonal of the affine quotient of `E'`, and
`f × f` is finite. So `g ≫ j` is finite, hence universally closed. Since
surjectivity is stable under base change, `j` is then universally closed as
well. So `j` is a closed immersion by Étale Morphisms, Lemma 41.7.2
(`04XV.html` in the first source). None of this is formalized here; the
proof is a separate unit.

# Affine quotients pull back along cartesian morphisms

Authors: Worker 239 and Worker 1224. Worker 239 supplied the shared Lean and
Markdown draft; Worker 1224 checked it against the cited sources and refined
the correspondence.

This module states, in the language of presentations of algebraic spaces by
étale equivalence relations, a consequence of descent of affine morphisms
along fpqc coverings (Stacks Project
[Lemma 35.37.1, Tag 0245](https://stacks.math.columbia.edu/tag/0245)). Let an
étale equivalence relation on an affine scheme map cartesianly to one on an
affine scheme with an affine quotient. Then it has an affine quotient. It
uses the definitions of `Langlands.AlgebraicGeometry.EtaleEquivalenceRelation`
unchanged (`EtaleEquivalenceRelation`, `EtaleEquivalenceRelation.IsCartesianHom`,
`EtaleEquivalenceRelation.HasAffineQuotient`) and the Mathlib class
`AlgebraicGeometry.IsAffine`. The module states the proposition and supplies
no proof.

## Formula and quantifiers

The declaration is
`Langlands.AlgebraicGeometry.EtaleEquivalenceRelationCartesianAffineQuotientStatement.{u}`.
Its defining formula is

```lean
def EtaleEquivalenceRelationCartesianAffineQuotientStatement : Prop :=
  ∀ (E E₀ : EtaleEquivalenceRelation.{u}) (f : E.U ⟶ E₀.U) (g : E.R ⟶ E₀.R),
    EtaleEquivalenceRelation.IsCartesianHom E E₀ f g → IsAffine E.U → IsAffine E₀.U →
      E₀.HasAffineQuotient → E.HasAffineQuotient
```

The universe `u` is arbitrary. The quantifiers range over all étale
equivalence relations `E` and `E₀` with schemes in `Scheme.{u}`, absolute
over `Spec ℤ`, and all morphisms `f : E.U ⟶ E₀.U` and `g : E.R ⟶ E₀.R`. The
hypotheses are:

- `IsCartesianHom E E₀ f g`: `g ≫ E₀.t = E.t ≫ f`, and the square formed by
  `g`, `E.s`, `E₀.s` and `f` is a pullback (Stacks Tag 0APD);
- `E.U` and `E₀.U` are affine;
- `E₀.HasAffineQuotient`: there are an affine scheme `M₀` and a flat, locally
  finitely presented, surjective `q₀ : E₀.U ⟶ M₀` such that `(E₀.t, E₀.s)`
  identifies `E₀.R` with `E₀.U ×_{M₀} E₀.U`.

The conclusion is `E.HasAffineQuotient`, the same property for `E`. The
hypothesis that `E₀.U` is affine makes `f` an affine morphism. The formula
does not mention the quotient map of `E` or its relation to `q₀`.

## Original source and correspondence

The statement is derived: it is not stated in this form in the literature.
The sources are:

- `stacks-noetherian-approximation-2026-11-01` (directory SHA-256
  `a9a500a6ecf5ab8155bccd57e5fff0616f581d41e9256563c7821a5b81019625`):
  `023V.html` (Definition 35.34.1: a descent datum for `V/X/S` is an
  isomorphism `V ×_S X → X ×_S V` over `X ×_S X` satisfying the cocycle
  condition), `0245.html` (Lemma 35.37.1: for an fpqc covering, descent data
  of schemes affine over the members are effective) and `02W5.html`
  (Lemma 35.39.1: for an fppf covering `{S_i → S}`, descent data relative to
  the covering correspond to sheaves `F` over `S` whose base changes
  `F ×_S S_i` are representable).
- `stacks-etale-equivalence-relations-2026-11-01` (directory SHA-256
  `df1ecbfa63c5e31cf736d9ea79dd262976c3098fd9b36f2dd32668d44bf75420`):
  `02WW.html` (Theorem 65.10.5: `U/R` is an algebraic space with `U → U/R`
  étale and surjective), `03C5.html` (Lemma 39.20.3: an fppf `q : U → M`
  with `R ≅ U ×_M U` makes `M` represent `U/R`), `07S3.html`
  (Lemma 39.20.7: for a cartesian morphism of equivalence relations,
  `U' = U ×_{U/R} U'/R'`) and `0APD.html` (cartesian morphisms).

The correspondence, which this module does not formalize, is as follows. Put
`Y = E.U/E.R` and `Y₀ = E₀.U/E₀.R` (`02WW`). By `03C5`,
`E₀.HasAffineQuotient` identifies `Y₀` with the affine scheme `M₀`, and
`q₀ : E₀.U → M₀` is flat, locally of finite presentation and surjective, so
`{E₀.U → M₀}` is an fppf, hence fpqc, covering. By `07S3` the cartesian
morphism `(f, g)` induces `Y → M₀` with `E.U = E₀.U ×_{M₀} Y`. So `Y` is a
sheaf over `M₀` whose base change to `E₀.U` is the scheme `E.U`. By `02W5` it
corresponds to a descent datum `(E.U/E₀.U, φ)` relative to `{E₀.U → M₀}`
(`023V`). The morphism `f : E.U → E₀.U` is a morphism of affine schemes,
hence affine, so this descent datum is effective by `0245`. The covering
consists of the single flat surjective morphism `q₀` of affine schemes, which
is the case to which the proof of `0245` reduces; there the descended object
is constructed as `Spec(C)` for a `Γ(M₀)`-algebra `C`. So there is a scheme
`V` affine over `M₀` with `V ×_{M₀} E₀.U ≅ E.U` compatibly with the descent
data. By the equivalence of `02W5` (its part (2)), `Y ≅ V`, so `Y` is an
affine scheme. As
in the Markdown of `EtaleEquivalenceRelationAffineDescentStatement`, the
étale surjection `E.U → Y` is then flat, locally of finite presentation and
surjective, and `E.R = E.U ×_Y E.U`. This is `E.HasAffineQuotient`.

In ring terms: write `A₀ = Γ(M₀)`, `B₀ = Γ(E₀.U)`, `C₀ = Γ(E₀.R)`, so
`C₀ = B₀ ⊗_{A₀} B₀`, and write `B = Γ(E.U)`. The cartesian square makes
`Γ(E.R) = C₀ ⊗_{B₀} B`. Faithfully flat descent along `A₀ → B₀` then shows
that `B = B₀ ⊗_{A₀} A` for `A = {b ∈ B : E.t^♯ b = E.s^♯ b}`, and the
quotient of `E` is `Spec A`.

## Scope and role

This statement is the last of three steps in the planned proof of
`EtaleEquivalenceRelationNoetherianApproximationStatement`. It is applied to
the cartesian morphism `E ⟶ E₁` given by
`EtaleEquivalenceRelationNoetherianCoverLevelStatement`, once the Noetherian
case `NoetherianEtaleEquivalenceRelationAffineDescentStatement` has made the
quotient of `E₁` affine. The proof is a separate unit. Possible tools in the
pinned Mathlib are `ModuleCat.comonadicExtendScalars`
(`Mathlib/Algebra/Category/ModuleCat/Descent.lean`: extension of scalars
along a faithfully flat ring map is comonadic) and the descent of
injectivity and surjectivity of ring maps in
`Mathlib/RingTheory/Flat/FaithfullyFlat/Descent.lean`.

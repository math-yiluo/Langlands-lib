# Schemeness of an algebraic space with an injective pair of maps to a scheme

Author: Worker 303.

This module derives two consequences of
`MonomorphismLocallyFiniteTypeSchemeStatement`. Both take that proposition as an
explicit hypothesis `hP1`, so nothing here depends on its proof. The module is
internal infrastructure for the proof of
`Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothRelationQuotientStatement`
(task `947bc5d5-327d-4b44-91e8-22c7382f065b`). There, the arrow space of the
relation is given by a pair of maps `s t` rather than by one monomorphism. It
imports `MonomorphismLocallyFiniteTypeSchemeStatement` and
`SmoothRelationQuotientStatement`, both unchanged.

All declarations are in namespace
`Langlands.AlgebraicGeometry.AlgebraicSpace.MonomorphismPairScheme`. Throughout,
`S : Scheme.{u}`, `F : Presheaf S` and `U : Over S`.

## The pair map

- `pairMap s t : F ⟶ (schemeYoneda S).obj (U ⨯ U)` for
  `s t : F ⟶ (schemeYoneda S).obj U`. Here `U ⨯ U` is the binary product in
  `Over S`, which exists because `Over S` has finite limits. On a section `r`
  over `T` it is `ULift.up (prod.lift (s.app T r).down (t.app T r).down)`, the
  lifted morphism `T ⟶ U ⨯ U` with components the two lifted morphisms
  `T ⟶ U` given by `s` and `t`. Naturality holds because both components are
  natural.
- `pairMap_app_down` (simp) records this formula.
- `mono_pairMap`: if for every `T : Over S` the map
  `r ↦ (s.app (op T) r, t.app (op T) r)` is injective, then `pairMap s t` is a
  monomorphism of presheaves. The proof checks injectivity objectwise
  (`NatTrans.mono_iff_mono_app`, `mono_iff_injective`): two morphisms to
  `U ⨯ U` are equal exactly when their composites with both projections are
  equal.
- `comp_pairMap`: if `b ≫ s = (schemeYoneda S).map s₀` and
  `b ≫ t = (schemeYoneda S).map t₀` for `b : (schemeYoneda S).obj W ⟶ F`, then
  `b ≫ pairMap s t = (schemeYoneda S).map (prod.lift s₀ t₀)`. This is checked
  on each lifted point with `prod.hom_ext`.

## The two consequences

`isRepresentedByScheme_of_injective_pair hP1 R s t inj b s₀ t₀ hb hbs hs ht hlft`
has the following hypotheses:

- `R : AlgebraicSpace S` and `s t : R.presheaf ⟶ (schemeYoneda S).obj U`;
- `inj`: for every `T : Over S`, the map `r ↦ (s.app (op T) r, t.app (op T) r)`
  on `R.sections T` is injective;
- `b : (schemeYoneda S).obj W ⟶ R.presheaf` with `IsEtale b` and
  `IsSurjective b`;
- `s₀ t₀ : W ⟶ U` with `b ≫ s = (schemeYoneda S).map s₀` and
  `b ≫ t = (schemeYoneda S).map t₀`;
- `LocallyOfFiniteType s₀.left`.

Its conclusion is `IsRepresentedByScheme R`. The proof applies `hP1` with
`Y = U ⨯ U`, `f = pairMap s t` (a monomorphism by `mono_pairMap`), the atlas
`b` and `w = prod.lift s₀ t₀` (the equation is `comp_pairMap`). The composite
of `w.left` with the first projection `(prod.fst : U ⨯ U ⟶ U).left` is
`s₀.left` (by `Over.comp_left` and `prod.lift_fst`), so `w.left` is locally of
finite type by Mathlib's `locallyOfFiniteType_of_comp`. Nothing is assumed
about `t₀` beyond the equation.

`isRepresentedByScheme_of_hasSmoothProjections hP1 R s t h hsm` takes the
hypotheses of `SmoothRelationQuotientStatement` on the arrow space:
`h : SmoothRelationQuotient.IsEquivalenceRelation R s t` and
`hsm : SmoothRelationQuotient.HasSmoothProjections R s t`. Its conclusion is
`IsRepresentedByScheme R`. The first component of `h T` is the injectivity
hypothesis. `hsm` supplies the atlas `b`, the morphisms `s₀ t₀` and smoothness
of `s₀.left`. Smoothness gives local finite type through Mathlib's instances,
so the previous theorem applies. The equivalence-relation part of `h` and the
smoothness of `t₀.left` are not used.

## Scope

This module proves no part of `MonomorphismLocallyFiniteTypeSchemeStatement`
itself. It only rewrites that proposition into the pair form used by the
smooth relation quotient proof.

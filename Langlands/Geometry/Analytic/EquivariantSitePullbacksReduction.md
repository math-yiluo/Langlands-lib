# Equivariant fibre products from localized analytic pullbacks

This module constructs the diagonal action on a supplied analytic pullback
and reduces the pullback existence statements for `Qét(X(G))` and `Ét(X(G))`
to nonequivariant analytic facts. The namespace is
`Langlands.Analytic.SaturatedAtlasPresentation`. The field universe `u`, the
common space and atlas-index universe `v`, and the group universe `z` are
independent. The ground field is complete and ultrametric, and the group has
an arbitrary topology as in `GSpace`.

## Diagonal action on a supplied pullback

`GSpace.pullbackOfForget` takes a cospan `f : A ⟶ S`, `g : B ⟶ S` of
`G`-spaces, a pullback square `IsPullback p q (forget.map f) (forget.map g)`
in the localized analytic category, and quasi-étaleness of `forget.map f`.
It returns a `GSpace` whose underlying analytic object is the given
pullback vertex `P`.

The equivariance equations for `f` and `g` let
`Langlands.CategoricalPullback.pullbackAction` induce the automorphism action
of `G` on `P`. The definition composes with `Aut.toEnd` to form Mathlib's
`Action` and uses extensionality on the underlying endomorphisms to recover
the automorphism action. The first conjunct of
`hasCompactPairPreimages_of_quasiEtale`, applied using Hausdorffness of `A`
and `B`, gives Hausdorffness of `P`. Continuity in the sense of
`IsContinuousAction` follows from
`isContinuousAction_of_isPullback_of_quasiEtale` using the continuity on
both factors and the two projection equations of the diagonal action.
`GSpace.pullbackOfForgetFst` and `GSpace.pullbackOfForgetSnd` package the
supplied analytic projections as `G`-morphisms using those same equations.

## Pullback witnesses over the base

`exists_equivariantSitePullback_of_isPullback` works in the full subcategory
of `G`-spaces over `X` whose underlying structure arrow has an analytic
morphism property `Q`, namely `(Q.inverseImage GSpace.forget).Over ⊤ X`.
It takes a supplied pullback square of the underlying cospan
`U₁ → U₃ ← U₂`, with quasi-étale first leg, and a proof of `Q` for the
composite `P → U₂ → X` on underlying analytic spaces. The diagonal action
makes `P` a `G`-space. The second equivariant projection followed by the
structure arrow of `U₂` supplies the structure arrow of the new object.
The pullback commutativity and both cospan triangles over `X` show that
composing the first projection with `U₁ → X` gives the same arrow.
Faithfulness of `GSpace.forget` lifts that equality to `GSpace`. This
makes both projections arrows over `X`. The resulting square has the
original analytic objects and arrows after forgetting the action, so the
supplied `IsPullback` proof gives exactly the required witness. This
construction does not require any closure property of `Q` itself.

## Conditional existence in the two sites

- `equivariantQuasiEtalePullbacks_of_stability` takes
  `QuasiEtaleCompStatement`, `QuasiEtaleBaseChangeStatement` and
  `QuasiEtaleOverMorphismStatement` for every ground field. The triangle for
  `U₁ → U₃` presents the quasi-étale structure arrow of `U₁` as a composite
  through the quasi-étale structure arrow of `U₃`. The over-morphism premise
  makes the first leg quasi-étale. The published
  `exists_localizedPullback_of_quasiEtale` then gives the underlying square.
  Base change makes the second projection quasi-étale, and composition makes
  its composite to `X` quasi-étale. The preceding construction supplies
  `EquivariantQuasiEtalePullbacksStatement`.
- `equivariantEtalePullbacks_of_localizedPullback` takes
  `LocalizedEtalePullbackStatement` and
  `AffinoidAtlasPresentation.StrongHom.EtaleRightCancellationStatement` for
  every ground field. The latter gives right cancellation for `strongEtale`
  by unfolding that property and applying the functorial composition equation
  for the canonical strong representatives. The published
  `etale_hasOfPostcompProperty_of_strong` transports cancellation to the
  localized morphism property, making `U₁ → U₃` étale by its triangle over
  `X`. The pullback premise supplies the square and the étale second
  projection. The published `etale_comp` certifies the composite to `X`,
  and `etale_le_quasiEtale` turns étaleness of the first leg into the
  quasi-étaleness needed by the diagonal-action construction. The result is
  `EquivariantEtalePullbacksStatement`.

## Provenance and scope

Internal construction. It combines the Library's categorical diagonal
action with its localized analytic theorems about supplied pullbacks,
then packages the data in the Library's equivariant over-categories.
The five analytic statements in the two conditional proofs are premises,
not results of this module. The pullback witnesses are certified in the
underlying analytic category; passage to limiting cones in the sites and
application to restriction are separate steps.

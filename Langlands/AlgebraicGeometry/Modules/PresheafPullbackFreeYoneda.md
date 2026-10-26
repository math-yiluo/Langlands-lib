# Pullback of free Yoneda module generators

For schemes `X Y : AlgebraicGeometry.Scheme.{u}`, a morphism `f : X ⟶ Y`,
and an open `V : Y.Opens`, this module defines, in
`Langlands.Scheme.Modules`, the isomorphism

```
presheafPullbackFreeYonedaIso f V : L(A_Y(V)) ≅ A_X(F(V)),
```

where `F = TopologicalSpace.Opens.map f.base`,
`A_Z(U) = (PresheafOfModules.free Z.ringCatSheaf.obj).obj (yoneda.obj U)`,
and `L` is the published `presheafPullback f`. All universes are arbitrary.
There are no additional hypotheses on `f`, the schemes, or the open.

## Construction and inverse identities

Write `U` for the published `presheafPushforward f`. The functor
`P ↦ (A_Y(V) ⟶ U(P))` has two explicit corepresentations:

- `e`, corepresented by `L(A_Y(V))`, is the one from
  `(presheafPullbackPushforwardAdjunction f).corepresentableBy`.
  Its equivalence is the pullback-pushforward adjunction bijection.
- `e'`, corepresented by `A_X(F(V))`, is Mathlib's
  `PresheafOfModules.pushforwardCompCoyonedaFreeYonedaCorepresentableBy`.
  Its equivalence evaluates a map from the free generator using
  `freeYonedaEquiv`, then uses the inverse free-generator equivalence on
  `Y`. The section modules have the same underlying elements after
  pushforward by restriction of scalars.

The definition supplies the maps explicitly:

```
hom = e.homEquiv.symm (e'.homEquiv (𝟙 _))
inv = e'.homEquiv.symm (e.homEquiv (𝟙 _)).
```

For `hom ≫ inv = 𝟙`, the proof applies injectivity of `e.homEquiv`,
uses its compatibility with composition, cancels its inverse, then uses
compatibility with composition of `e'` in reverse. The result is the
inverse law for `e'.homEquiv`. For `inv ≫ hom = 𝟙`, it interchanges
`e` and `e'`. Thus both inverse identities follow from the supplied
bijections and their naturality, with no invertibility assumption on a
pullback tensor comparison.

## Basis and unit laws

`presheafPullbackFreeYonedaIso_homEquiv` identifies the adjunction image
of `hom` with `freeYonedaEquiv.symm` of the identity basis section in
`A_X(F(V))`. It cancels the adjunction equivalence and its inverse, and
then reduces the free-generator equivalence at the identity map.

`presheafPullbackFreeYonedaIso_hom_unit` evaluates that formula at `V`:
the unit's distinguished section, followed by `hom`, is the identity
basis at `F(V)`. Its proof uses Mathlib's
`freeYonedaEquiv_symm_app`.

`presheafPullbackFreeYonedaIso_hom_unit_app` gives the restriction formula.
For an inclusion `i : U₀ ⟶ V`, the unit applied to the free basis indexed
by `i`, followed by the component of `hom` at `F(U₀)`, is the free basis
indexed by `F.map i`. The proof uses naturality of the adjunction image,
the preceding identity-basis formula, and `ModuleCat.freeDesc_apply` to
compute restriction of a free basis.

`presheafPullbackFreeYonedaIso_inv_basis` says that `inv` sends the identity
basis at `F(V)` to the unit's identity-basis section. It applies `inv` to
the forward basis formula and cancels `hom ≫ inv` using the constructed
isomorphism law.

## Provenance and scope

This is internal derived mathematical infrastructure implemented by Worker 536,
using the supplied Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`
in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`. The inputs are the
pinned Mathlib modules `Algebra/Category/ModuleCat/Presheaf/Pullback.lean`,
`Generator.lean`, `Free.lean`, and the adjunction/corepresentation APIs.
It is not a transcription of an external source theorem.

The imported Library module
`Langlands.AlgebraicGeometry.Modules.PresheafPullbackTensor` and all its
imports are unchanged. The ring morphism is written with explicit source
and target presheaves as `Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)`,
the same morphism used by the published functor aliases. The elaboration
option `backward.isDefEq.respectTransparency false` permits unfolding the
existing category presentations and adds no assumption.

This module identifies pullback on individual free generators. The tensor
comparison on generator pairs and the unrestricted comparison remain separate
constructions and proofs.

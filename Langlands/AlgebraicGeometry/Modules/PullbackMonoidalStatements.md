# Monoidality of the existing pullback comparisons

The three Prop-valued definitions in this module specify the remaining
identity and composition compatibility for the canonical strong symmetric
monoidal pullback constructed in `PullbackMonoidal`. They quantify over
actual schemes in an arbitrary universe `u` and use the existing natural
isomorphisms from `AlgebraicGeometry.Scheme.Modules`. No new comparison
isomorphisms or assumed coherence instances are introduced.

`PullbackIdentityMonoidalStatement` says that for every scheme `X`, the
forward natural transformation of `Scheme.Modules.pullbackId X`, from
pullback along the identity of `X` to the identity functor on `X.Modules`,
is monoidal. The identity functor has its usual monoidal structure.

`PullbackCompositionMonoidalStatement` says that for every pair
`f : X ⟶ Y`, `g : Y ⟶ Z`, the forward natural transformation of the
existing `Scheme.Modules.pullbackComp f g`, from
`Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback f` to
`Scheme.Modules.pullback (f ≫ g)`, is monoidal. The source has the monoidal
structure induced by functor composition and the two canonical pullbacks;
the target has the canonical structure for the composite scheme map.

For each such transformation `τ : F ⟶ G`, the precise meaning is
`CategoryTheory.NatTrans.IsMonoidal τ` from pinned Mathlib's
`CategoryTheory/Monoidal/NaturalTransformation.lean`. Its fields are

- `ε F ≫ τ.app (𝟙_) = ε G` for the lax unit maps;
- `μ F M N ≫ τ.app (M ⊗ N) = (τ.app M ⊗ₘ τ.app N) ≫ μ G M N`
  for every pair of module sheaves `M,N`.

The lax maps of the scheme pullbacks are the inverses of the fixed canonical
oplax maps, as identified by the four formulas in `PullbackMonoidal`.
Mathlib also derives monoidality of the inverse of a monoidal natural
isomorphism from monoidality of its forward map.

`PullbackComparisonsMonoidalStatement` is exactly the conjunction of the
identity and composition statements in the same universe. This module
specifies the equations and does not prove them. They form an internal
categorical specification of the already constructed maps, using the
conventions of the pinned Mathlib sources above; there is no separate
external literature assertion.

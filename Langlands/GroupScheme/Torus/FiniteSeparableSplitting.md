# Finite separable splitting from a separable-closure splitting

Author: Worker 27.

This module supplies the finite-stage step for the finite Galois splitting proof.
For a group scheme `G` over `Spec k`, it assumes that the structure morphism of
`G` is quasi-compact and quasi-separated and that `G` becomes split over the
separable closure of `k`. It constructs a finite intermediate field of that
closure over which `G` is split, and packages its underlying field as a finite
separable extension of `k`. All fields and the resulting field witness lie in
one arbitrary universe `u`.

The existence of a separable-closure splitting is an input to this module. The
module does not prove that every actual torus has such a splitting, or produce
the finite Galois enlargement. Those are separate steps in the host proof.

## Public construction and results

The namespace is `Langlands.GroupScheme`. Write `G_K` for
`(GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G`.
Base changes and isomorphisms here are the existing actual group schemes in
`Grp (Over (Spec k))`.

- `IsSplitTorus.exists_finiteIntermediateField_of_algebraic k Ω G h`: if
  `Ω / k` is algebraic, the structure morphism of `G` is quasi-compact and
  quasi-separated, and `h : IsSplitTorus G_Ω`, then there is
  `E : Langlands.AlgebraicGeometry.Picard.FinIntermediateField k Ω` with
  `IsSplitTorus G_E`. This finite-intermediate-field type is the published
  subtype `{E : IntermediateField k Ω // FiniteDimensional k E}`.
- `IsSplitTorus.finiteSeparableSplittingField k G h`: for
  `h : IsSplitTorus G_(SeparableClosure k)` and the same two geometric
  hypotheses, this definition uses `Classical.choose` on the preceding result
  to select an element of `FinIntermediateField k (SeparableClosure k)`.
  The choice is not asserted to be canonical or minimal.
- `IsSplitTorus.finiteSeparableSplittingField_isSplit k G h`: the selected
  intermediate field has the splitting property, by `Classical.choose_spec`.
- `IsSplitTorus.exists_finiteSeparable_of_separableClosure k G h`: there are
  `K : Type u`, a `Field K`, and an `Algebra k K` such that
  `FiniteDimensional k K`, `Algebra.IsSeparable k K`, and `IsSplitTorus G_K`.
  The witness is the underlying field of the selected intermediate field.
  Its finite-dimensionality is the subtype's second component; separability
  is inherited from `SeparableClosure k` through the intermediate-field tower.

No perfectness, characteristic, infinitude, positive-rank or affineness
hypothesis is used. The finite index type in a splitting may be empty. The
geometric hypotheses are on the original structure morphism; no finite
presentation hypothesis on `G` is assumed.

## Implemented finite-stage argument

The private lemma `exists_finite_stage_map` works more generally with group
schemes `G` and `H` over `Spec k`. It assumes quasi-compactness and
quasi-separatedness of `G`, local finite presentation of `H`, algebraicity of
`Ω / k`, and a morphism of the underlying schemes over `Spec Ω`,
`f : G_Ω.X ⟶ H_Ω.X`.

The published module
`Langlands.AlgebraicGeometry.Picard.IntermediateFieldBaseChangeLimit` realizes
`G_Ω` as the limit of `G_E` over finite intermediate fields, with affine
transition maps and quasi-compact, quasi-separated stages. Compose `f` with the
projection to `H`. Mathlib's
`Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation` factors that map
through some `G_E`, compatibly with its structure morphism to `Spec k`.
The pullback universal property then gives a map `g : G_E.X ⟶ H_E.X` over
`Spec E`. The lemma records equality after composition with the limit
projections.

To recover the group structure and invertibility at this same finite stage,
`exists_finite_stage_iso` applies this factorization to the forward map of an
isomorphism `G_Ω ≅ H_Ω`. The private tower comparisons
`overPullbackTowerIso`, `baseChangeTowerIso` and `finiteStageBaseChangeIso`
identify direct base change to `Ω` with base change first to `E` and then to
`Ω`. Their first-projection identities turn the factorization equality into
commutativity in `Over (Spec Ω)`.

The private lemma `group_iso_of_fpqc_pullback_compat` expresses this last
argument with abstract group schemes and comparison isomorphisms. It shows
that the pullback of `g` is the underlying map of a group-scheme isomorphism.
Pullback along `Spec Ω ⟶ Spec E` is faithful and monoidal, so the unit and
multiplication equations reflect to `g`; this is the private lemma
`isMonHom_of_faithful_map`. The same base morphism is surjective, flat and
quasi-compact. Mathlib's fpqc descent of isomorphisms, followed by reflection
through `Over.forget`, therefore makes `g` an isomorphism. Finally `Grp.mkIso`
packages it as a group-scheme isomorphism. This proves the private
`exists_finite_stage_iso` without separately spreading an inverse.

For `IsSplitTorus.exists_finiteIntermediateField_of_algebraic`, unpack the given
splitting as a finite index type `I` and an isomorphism with the split torus over
`Ω`. The published `splitTorus.baseChangeIso` identifies this target with the
base change of `splitTorus (Spec k) I`. That split torus is smooth, hence locally
of finite presentation, so the preceding finite-stage isomorphism argument
applies. At the resulting field `E`, base change of the split torus remains
split; `IsSplitTorus.of_iso` transfers this property to `G_E`.

## Provenance

This is an internal derived construction rather than a transcription of a
numbered result from the torus literature. Its ingredients are the published
finite-intermediate-field limit construction, the published split-torus and
base-change interfaces, and Mathlib's scheme factorization and fpqc descent
results. The additional argument combines those interfaces and reflects the
group-object laws along faithful pullback. The chosen field and its existential
packaging make precisely that conditional finite-stage conclusion available to
the host proof.

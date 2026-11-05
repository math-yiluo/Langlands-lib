# Levi points of an actual rational parabolic

Author: Worker 6. Module `Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints`, namespace `Langlands.Aubert.General.RepresentedParabolic`.

This module identifies the rational points `M(F)` of a rational Levi subgroup, with their own canonical topology, with the literal Levi image `pointImage (l ≫ p)` inside `G(F)`. It then transports the published normalized induction and Jacquet functors of the represented-parabolic interface to smooth representations of `M(F)` itself. Renard works with `M` as a subgroup of `G` throughout. The published interface realizes the Levi as the image subgroup `pointImage (l ≫ p)`, while the published temperedness predicate `IsNormalizedExponentTempered` applies to representations of the points of a connected reductive group scheme. This module connects the two, as needed for statements about tempered representations of Levi subgroups (Renard VII.2.2–VII.2.6, printed pp.227–231 / PDF pp.233–237; registered source `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`).

It is implementation content: the source treats `M(F)` as a subgroup of `G(F)` and needs no such identification. No representation-theoretic result is proved here.

## Generic lemmas

- `pointImage_eq_range_carrier j` states that `pointImage j`, the range of `rationalPoints.map j`, equals the carrier on the identity test scheme of the range subgroup functor `SubgroupFunctor.range j`. Membership in both means `∃ y, y ≫ j.hom.hom = x`, so the proof is `Iff.rfl` after extensionality.
- The imported `GroupScheme.IsClosedSubgroup.comp` states that a composite of closed subgroups is a closed subgroup, because closed immersions compose.
- The imported `GroupScheme.IsClosedSubgroup.isRepresentedBy_range` states that a closed subgroup represents its range subgroup functor. The monomorphism comes from the closed immersion, and the range equality is reflexivity.
- `subgroupCongrContinuous h : H ≃ₜ* K` is Mathlib's `MulEquiv.subgroupCongr` for an equality `h : H = K` of subgroups of a topological group, with both directions continuous because they are inclusions of subtypes.

## The Levi point isomorphism

The rest of the module assumes a field `k` with `[Field k] [TopologicalSpace k]` and `[IsAffineHom G.X.hom]`, and puts the canonical topology `RationalPointFamily.pointTopology` on `rationalPoints G`.

`leviPointTopology l hl` is the canonical topology `RationalPointFamily.pointTopology` on `rationalPoints M`. The affine structure morphism it needs comes from `hl.isConnectedReductive`, the connected reductivity of the Levi recorded in `IsRationalLeviSubgroup`. The published `IsNormalizedExponentTempered`, applied to `M` with this affine instance, uses the same canonical topology.

For `p : P ⟶ G` with `hp : IsParabolicSubgroup p` and `l : M ⟶ P` with `hl : IsRationalLeviSubgroup l`,

`leviPointsEquiv p l hp hl : rationalPoints M ≃ₜ* pointImage (l ≫ p)`

is an isomorphism of topological groups. The source carries `leviPointTopology l hl`, and the target carries the subspace topology from `G(F)`. It is the published `rationalPointSubgroupHomeomorph` for the closed subgroup `l ≫ p` and its range functor, followed by `subgroupCongrContinuous` for `pointImage_eq_range_carrier`. The published construction shows that the point map of a closed immersion is a topological embedding, so the canonical topology of `M(F)` is the subspace topology of its image. `leviPointsEquiv_apply_coe` states, by `rfl`, that the underlying point of `G(F)` is `rationalPoints.map (l ≫ p) m`.

Two consequences give the instances that the published exponent and temperedness interfaces require for `M(F)`:

- `leviPoints_locallyCompactSpace` (with `[T2Space k]` and `[LocallyCompactSpace (rationalPoints G)]`): `M(F)` is locally compact. The Levi image is closed by the published `isClosed_leviPoints`, so it is locally compact, and `leviPointsEquiv` is a closed embedding into it.
- `leviPoints_nonarchimedeanGroup` (with `[NonarchimedeanGroup (rationalPoints G)]`): `M(F)` is a nonarchimedean group. The Levi image is nonarchimedean by the published subgroup instance. `M(F)` is a topological group because `leviPointsEquiv` is an inducing group isomorphism, and Mathlib's `NonarchimedeanGroup.nonarchimedean_of_emb` applies to the open embedding `leviPointsEquiv.symm`.

## Transported functors

Under `[T2Space k] [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]`, for a matching geometric unipotent radical `r : U ⟶ P` with `hr` and `hmul : IsIso (subgroupMultiplication l r)`:

- `leviInductionFunctor p l r hp hr hl hmul : SmoothRep.{0, u, v} ℂ (rationalPoints M) ⥤ SmoothRep.{0, u, max u v} ℂ (rationalPoints G)` is the published `SmoothRep.pullbackFunctor` along `(leviPointsEquiv p l hp hl).symm`, followed by the published `inductionFunctor p l r hp hr hl hmul`. This is Renard's normalized induction `i_P^G` of VI.1.2 (printed pp.135–136 / PDF pp.141–142), applied to a representation of `M(F)`. The universe change to `max u v` is that of the published induction functor. `leviInductionFunctor_obj` records the object formula by `rfl`.
- `leviJacquetFunctor p l r hp hr hl hmul : SmoothRep.{0, u, v} ℂ (rationalPoints G) ⥤ SmoothRep.{0, u, v} ℂ (rationalPoints M)` is the published `jacquetFunctor p l r hp hr hl hmul`, followed by pullback along `leviPointsEquiv p l hp hl`. This is Renard's normalized Jacquet functor `r_P^G`, with values in representations of `M(F)`. `leviJacquetFunctor_obj_representation` records by `rfl` that `m ∈ M(F)` acts through `leviPointsEquiv p l hp hl m`.

The normalizations are those of the published functors, whose Markdown explains the modulus convention. Pullback along a topological-group isomorphism keeps the carrier and composes the action, so it changes no normalization.

## Scope

No statement about temperedness, exponents, adjunction, exactness or admissibility of the transported functors is made here. Those are separate statement units. The local compactness and nonarchimedean-group instances of `G(F)` are hypotheses, as in the published represented-parabolic interface.

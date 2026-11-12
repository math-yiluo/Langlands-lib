# Affineness of homogeneous quotients along a normal subgroup tower

Authors: Worker 1497.

Let `M ⊆ H ⊆ G` be group schemes, with `i : H ⟶ G` and `j : M ⟶ H`. This module
compares homogeneous quotients `G/M` and `G/H` (the structure
`HomogeneousQuotientFromEmbedding.HomogeneousQuotient`). It shows that
`G/M ×_{G/H} G ≅ G × H/M`. Over a field it concludes that `G/M` is affine when
`G/H` is affine and `M` is normal in `H`.

## Provenance

This is a standard step in the proof that a closed subgroup `H` of a reductive group
with affine quotient `G/H` is reductive. It is used in the reduction from `H` to its
identity component and then to a normal unipotent subgroup `N` of `H⁰`. The
statements here are internal helper results for the proof of
`Langlands.GroupScheme.AffineHomogeneousQuotientReductiveStatement`. They are not
transcriptions of a cited theorem. The geometric content is the following: the map
`G/M ⟶ G/H` is, after base change along `G ⟶ G/H`, the projection
`G × H/M ⟶ G`. Then `H/M` is affine because it is an affine group quotient, and
affineness descends along the faithfully flat map `G ⟶ G/H`.

## Declarations over an arbitrary base `S`

All of these are in the namespace `Langlands.GroupScheme.HomogeneousQuotientTower`.
Here `i : H ⟶ G`, `j : M ⟶ H`, `QM : HomogeneousQuotient (j ≫ i)`,
`QH : HomogeneousQuotient i` and `Q' : HomogeneousQuotient j`. The arrow scheme
`arrows i = G × H` and its maps `source i : (g, h) ↦ g` and
`target i : (g, h) ↦ g · i(h)` are from `HomogeneousCosetRelation`.

- `cosetWitness D a b h`, with `cosetWitness_spec`: for `D : HomogeneousQuotient i`
  and points `a b : T ⟶ G` with the same image in `D`, a point of `H` whose image
  under `i` is `a⁻¹ * b`. It is chosen from the field `D.fibers`.
- `isPullback_source_target [Mono i.hom.hom] D`: the square with `source i`,
  `target i` and two copies of `D.projection` is a pullback. So `G × H` is the
  kernel pair of `G ⟶ G/H`. The lift of `(a, b)` is `(a, cosetWitness D a b _)`.
  Uniqueness is the published `HomogeneousCosetRelation.arrow_unique`.
- `mem_range_comp_iff [Mono i.hom.hom] j x`: for `x : T ⟶ H`, `i ∘ x` lies in the
  range of `j ≫ i` if and only if `x` lies in the range of `j`.
- `fiber_le`: points with the same image in `G/M` have the same image in `G/H`.
- `towerMap j QM QH : QM.scheme ⟶ QH.scheme`, with
  `projection_towerMap : QM.projection ≫ towerMap j QM QH = QH.projection`. It is the
  published descent `HomogeneousQuotientComparison.desc` of `QH.projection` along
  `QM.projection`, using `fiber_le`.
- `towerArrow j QM QH : arrows i ⟶ pullback (towerMap j QM QH) QH.projection`, the
  map `(g, h) ↦ (q_M(g · i(h)), g)`, with the simp lemmas `towerArrow_fst` and
  `towerArrow_snd`.
- `isPullback_towerArrow`: the square with `towerArrow`, `target i`,
  `pullback.fst` and `QM.projection` is a pullback. Proof: paste it on top of the
  pullback square defining the fibre product (`IsPullback.of_bot`). The outer
  rectangle is the kernel pair square of `isPullback_source_target` for `QH`.
- `effectiveEpi_towerArrow`: `towerArrow` is a base change of `QM.projection`. That
  map is smooth (hence flat), surjective and quasi-compact, so `towerArrow` is too.
  Such morphisms are effective epimorphisms in Mathlib.
- `effectiveEpi_tensorHom`: `𝟙 G ⊗ Q'.projection : G × H ⟶ G × H/M` is
  quasi-compact, flat and surjective, by `MorphismProperty.pullbackMap`. So it is
  an effective epimorphism.
- `towerArrow_eq_iff`: two points `a, b` of `G × H` have the same image under
  `towerArrow` if and only if they have the same image under
  `𝟙 G ⊗ Q'.projection`. Write `a = (g, h)` and `b = (g', h')`. Both sides say
  `g = g'` together with a condition on `h` and `h'`. On the left the condition is
  `(g · i(h))⁻¹ · (g · i(h')) = i(h⁻¹ h') ∈ range (j ≫ i)`, by `QM.fibers`. On the
  right it is `h⁻¹ h' ∈ range j`, by `Q'.fibers`. These agree by
  `mem_range_comp_iff`.
- `towerPullbackIso j QM QH Q' : pullback (towerMap j QM QH) QH.projection ≅ G ⊗ Q'.scheme`:
  the published `HomogeneousQuotientComparison.iso` applied to the two effective
  epimorphisms `towerArrow` and `𝟙 G ⊗ Q'.projection` out of `G × H`. Their fibres
  agree by `towerArrow_eq_iff`.

The local instances of the module record the smoothness, surjectivity and
quasi-compactness fields of the three quotient projections.

## Theorems over a field

Let `k` be a field and `G H M` group schemes over `Spec k`.

```
isAffineHom_of_normal [IsAffineHom G.X.hom] (i : H ⟶ G) (hi : IsClosedSubgroup i)
    (hH : Smooth H.X.hom) (j : M ⟶ H) (hj : IsClosedSubgroup j) (hM : Smooth M.X.hom)
    (hn : (SubgroupFunctor.range j).IsNormal) (QH : HomogeneousQuotient i)
    (hQH : IsAffineHom QH.scheme.hom) (QM : HomogeneousQuotient (j ≫ i)) :
    IsAffineHom QM.scheme.hom
```

So if `G` is affine, `H` is a smooth closed subgroup, `M` is a smooth closed normal
subgroup of `H`, and some homogeneous quotient `G/H` is affine, then every
homogeneous quotient `G/M` is affine. `G` is not assumed smooth.

Proof.

1. `H` is affine over `k`: `i` is a closed immersion, which is affine, and
   `G ⟶ Spec k` is affine (rewrite by `Over.w`). `i.hom.hom` is a monomorphism
   (`Over.mono_of_mono_left`).
2. **`H/M` is affine.** The published `smoothSubgroupQuotientExistence` gives a
   homogeneous quotient `Q' : HomogeneousQuotient j`. Since the range of `j` is
   normal, `Q'.groupScheme hn` is a group scheme and `Q'.groupProjection hn` is a
   group homomorphism whose underlying map is `Q'.projection`
   (`HomogeneousQuotientGroup`). The projection is smooth, surjective and
   quasi-compact, and `H` is of finite type and affine. So the published
   `affineGroupSchemeQuotient` gives `IsAffineHom Q'.scheme.hom`.
3. **The fibre product is affine.** `G`, `H/M` and `Spec k` are affine, so
   `G × H/M` is affine. By `towerPullbackIso`, so is
   `pullback (towerMap j QM QH) QH.projection`.
4. **Descent.** `QH.projection` is smooth (hence flat) and surjective, and `G` and
   `G/H` are affine. Apply
   `Langlands.AlgebraicGeometry.FaithfullyFlatAffineDescent.isAffine_of_isPullback`
   to the image under `Over.forget` of the pullback square of `towerMap` and
   `QH.projection`. It gives that `QM.scheme.left` is affine. A morphism from an
   affine scheme to the affine scheme `Spec k` is affine.

```
isAffineHom_identityComponent [IsAffineHom G.X.hom] (i : H ⟶ G)
    (hi : IsClosedSubgroup i) [Smooth H.X.hom] [IsAffineHom H.X.hom]
    (QH : HomogeneousQuotient i) (hQH : IsAffineHom QH.scheme.hom)
    (Q₀ : HomogeneousQuotient (identityComponentι H ≫ i)) :
    IsAffineHom Q₀.scheme.hom
```

This is `isAffineHom_of_normal` with `M = identityComponent H` and
`j = identityComponentι H`. The published
`IdentityComponent.isClosedSubgroup_identityComponentι` and
`IdentityComponent.isNormal_range_identityComponentι` give that `H⁰` is a closed
normal subgroup of `H`. Its smoothness is the published instance for the identity
component of a smooth group.

```
isAffineHom_of_normal_identityComponent [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (i : H ⟶ G) (hi : IsClosedSubgroup i) [Smooth H.X.hom] [IsAffineHom H.X.hom]
    (QH : HomogeneousQuotient i) (hQH : IsAffineHom QH.scheme.hom)
    {N} (j : N ⟶ identityComponent H) (hj : IsClosedSubgroup j) (hN : Smooth N.X.hom)
    (hn : (SubgroupFunctor.range j).IsNormal)
    (QN : HomogeneousQuotient (j ≫ identityComponentι H ≫ i)) :
    IsAffineHom QN.scheme.hom
```

This is the two-step tower `N ◁ H⁰ ◁ H`, for a smooth closed normal subgroup `N` of
`H⁰`. Here `G` is also assumed smooth. The composite `identityComponentι H ≫ i` is a
closed immersion, as a composite of two closed immersions. The published
`smoothSubgroupQuotientExistence` then gives a homogeneous quotient
`Q₀ : HomogeneousQuotient (identityComponentι H ≫ i)`. It is affine by
`isAffineHom_identityComponent`. Then `isAffineHom_of_normal`, applied to `j` inside
`H⁰ ⟶ G` and to `Q₀`, gives the claim.

# Radical weights of a geometric-lemma intersection datum

Fix a field `k`, a group scheme `G` over `k`, represented parabolics `P = M N`
and `Q = L U` of `G`, and a point `z ∈ G(k)`. Let `D` be a
`GeometricLemmaIntersectionDatum` for `z`
(`Langlands/Representation/Geometric/RepresentedGeometricLemmaStatement.lean`).
It provides the parabolic `P' = M ∩ zQz⁻¹` of `M` with Levi `M' = M ∩ zLz⁻¹`
and unipotent radical `N' = M ∩ zUz⁻¹`, the parabolic `Q' = L ∩ z⁻¹Pz` of `L`
with Levi `L'`, and an isomorphism `φ : L' ≅ M'` whose composite into `G` is
conjugation by `z`.

This internal supporting module shows that conjugation by `z⁻¹` carries the
torus weights on the radical `N'` to torus weights on the radical `U`. For split
components it follows that intrinsic positive roots of `P'` restrict to
intrinsic positive roots of `Q`, and that restriction maps the nonnegative
restricted-root cone of `P'` into the cone of `Q`.

## Declarations

Two general lemmas are in the namespace `Langlands.GroupScheme.RelativeRoot`.

- `actionWeightSupport_conjugation_range_comp`: for a torus `i : S → H`, a
  subgroup `g : K → H` and a monomorphism `j : H → G`, the conjugation weights
  of `i ≫ j` on the image of `g ≫ j` equal the conjugation weights of `i` on the
  image of `g`.
- `comp_mem_actionWeightSupport_conjugation`: if `χ` is a conjugation weight of
  a torus `i : S → G` on a subgroup functor `F`, then for every morphism of tori
  `τ : S' → S` the character `τ ≫ χ` is a conjugation weight of
  `groupHom τ ≫ i` on `F`.

The other declarations are in the namespace
`Langlands.Aubert.General.RepresentedParabolic.GeometricLemmaIntersectionDatum`.
In all of them `a : A → L` and `a' : A' → L'` are torus maps, and
`τ : A → A'` satisfies `groupHom τ ≫ a' ≫ (L' → L) = a`.

- `comp_mem_actionWeightSupport_radical`: if `β` is a conjugation weight of the
  torus `a' ≫ φ ≫ (M' → M)` on the image of `N' → M`, then `τ ≫ β` is a
  conjugation weight of `a ≫ (L → G)` on the image of `U → G`. It assumes that
  `G` and `M` are affine over `k`.
- `comp_mem_intrinsicPositiveRoots`: let `presQ` be a parabolic root
  presentation of `(q, lQ, a)` and `presM` one of `(p', l', a' ≫ φ)`. If `β` is
  an intrinsic positive root of `presM`, then `τ ≫ β` is an intrinsic positive
  root of `presQ`. It also assumes that `G` and `M` are smooth.
- `restrictReal_mem_nonnegCone`: in the same situation, with `G` and `M` also
  locally of finite type, assume that the ambient relative roots of `presQ` are
  closed under negation. Then for every `x` in the nonnegative cone of `presM`,
  the real restriction `rationalCharacterRestrictReal (groupHom τ) x` lies in the
  nonnegative cone of `presQ`.

The split components used later come from `exists_isSplitComponent_factor` in
`GeometricLemmaSplitComponent.lean`. It gives `a'` and a factor `f : A_L → A_{L'}`
with `f ≫ a' ≫ (L' → L) = a`, which is the hypothesis on `τ` above.

## Proofs

- `actionWeightSupport_conjugation_range_comp` applies `actionWeightSupport_map`
  to the monomorphism `j`; the needed equivariance is `conjugation_act_comp`.
  This gives the claim for the subgroup functor `(range g).map j`. Writing
  `range g` as `⊤.map g` (`SubgroupFunctor.map_top`) and composing the maps
  (`SubgroupFunctor.map_comp`) turns it into `range (g ≫ j)`.
- `comp_mem_actionWeightSupport_conjugation` keeps the same tangent vector and uses
  `mem_weightSpace_precomp_torus_hom` on its weight space.
- `comp_mem_actionWeightSupport_radical` has four steps.
  1. The inclusion `M → G` is a monomorphism, because `M → P` and `P → G` are
     closed subgroups. The first general lemma moves the weight from `M` to `G`:
     `β` is a weight of the torus `a' ≫ φ ≫ (M' → G)` on the image of `N' → G`.
  2. The field `radical_eq` of `D` writes the image of `N' → G` as the
     intersection of the image of `M → G` with the image of
     `rQ ≫ q ≫ innerIso z`. So it lies in the second image, and
     `actionWeightSupport_mono` moves `β` to the image of `U` conjugated by `z`.
  3. The field `φ_comp` rewrites the torus as
     `(a' ≫ (L' → G)) ≫ innerIso z`. Since `innerIso z` is an isomorphism, hence
     a monomorphism, the first general lemma removes it from both the torus and
     the subgroup. Then `β` is a weight of `a' ≫ (L' → G)` on the image of
     `U → G`.
  4. The second general lemma restricts along `τ`, and the hypothesis on `τ`
     identifies `groupHom τ ≫ a' ≫ (L' → G)` with `a ≫ (L → G)`.
- `comp_mem_intrinsicPositiveRoots` uses
  `intrinsicPositiveRoots_eq_subgroupRelativeRoots`: an intrinsic positive root
  of `presM` is a nonzero conjugation weight on the image of the radical
  `N' → M`. The previous theorem gives that `τ ≫ β` is a weight on the image of
  `U → G`. By `range_comp_radical_eq`, that image is the dynamic unipotent
  subgroup of the split-component cocharacter of `presQ`, and
  `actionWeightSupport_dynamicUnipotent` identifies its weights with the positive
  relative roots for that cocharacter. These are the intrinsic positive roots of
  `presQ` by definition.
- `restrictReal_mem_nonnegCone`: by `restrictedRootNonnegCone_eq_hull` the cone
  of `presM` is the span over the nonnegative reals of its restricted simple
  roots, and the proof is an induction on that span. A restricted simple root
  equals `1 ⊗ β` for an intrinsic positive root `β`
  (`restrictedRoots_subset_image_intrinsicPositiveRoots`). Its restriction is
  `1 ⊗ (τ ≫ β)` (`rationalCharacterRestrictReal_tmul`). By the previous theorem
  `τ ≫ β` is an intrinsic positive root of `presQ`, so
  `one_tmul_mem_nonnegCone_of_mem_intrinsicPositiveRoots` from
  `Langlands/GroupScheme/Rational/IntrinsicRootCone.lean` puts it in the cone of `presQ`. This step uses the
  negation hypothesis. Restriction is linear, and the cone contains zero and is
  closed under addition and nonnegative scaling.

## Provenance and scope

This is derived content for the proof of Renard VII.2.2
(`LeviInductionNormalizedTemperedStatement`). Renard compares the exponents of
the pieces of the geometric lemma with the cone of `Q` through the set `W_{L,M}`
(Renard, *Représentations des groupes réductifs p-adiques*, VII.2.2, PDF
pp.233–234). This module replaces that comparison: the radical `N'` of `P'` is
contained in `zUz⁻¹`, so conjugation by `z⁻¹` sends its weights into the weights
of `U`. The negation hypothesis on the relative roots of `presQ` stays explicit;
the module does not prove it.

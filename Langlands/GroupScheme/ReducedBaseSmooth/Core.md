# A closed subscheme of a smooth scheme with fibres of full dimension along a section

Author: Worker 9.

Helper module for the proof of
`Langlands.GroupScheme.ReducedBaseConnectedFibreSmoothStatement` (SGA 3, Exposé VI_B,
Corollaire 4.4, reduced locally Noetherian base, connected fibres). Its main theorem,
`exists_smooth_open_of_closedImmersion`, says the following. Let `Y` be a closed subscheme of
a scheme `Z` that is smooth of relative dimension `n` over a reduced base `T`. Suppose `Y → T`
has a section and every fibre of `Y → T` is smooth of the same relative dimension `n`. Then
`Y → T` is smooth on an open neighbourhood of the section. This is the step that uses
reducedness of the base.

All declarations are in the namespace `Langlands.GroupScheme.ReducedBaseSmooth`, and all
schemes lie in one universe `u`. `SectionComponent` refers to the Library namespace
`Langlands.AlgebraicGeometry.SectionComponent`.

## Declarations

- `injective_of_surjective_of_ringKrullDim_eq`: let `f : A →+* B` be a surjective ring map,
  where `A` is a domain, and suppose `ringKrullDim A = ringKrullDim B = n` for a natural
  number `n`. Then `f` is injective.
- `connectedComponent_subset_range_of_closedImmersion`: let `k` be a field and
  `j : X' ⟶ X` a closed immersion of `k`-schemes, with `f : X ⟶ Spec k` and
  `f' : X' ⟶ Spec k` both `SmoothOfRelativeDimension n`. Let `x'` be a closed point of `X'`.
  Then the connected component of `X` through `j x'` lies in the range of `j`. The Lean
  statement does not require `f' = j ≫ f`.
- `fiberMap p i t : (i ≫ p).fiber t ⟶ p.fiber t`: for `p : Z ⟶ T`, `i : Y ⟶ Z` and `t : T`,
  the morphism of residue fibres over `t` induced by `i`. The lemmas `fiberMap_fiberι` and
  `fiberMap_fiberToSpecResidueField` express its compatibility with the fibre inclusions and
  with the projections to `Spec κ(t)`. An instance records that `fiberMap p i t` is a closed
  immersion when `i` is.
- `comp_section`: if `e ≫ i ≫ p = 𝟙 T`, then `(e ≫ i) ≫ p = 𝟙 T`.
- `fiberSection_comp_fiberMap` and `fiberMap_fiberPoint`: `fiberMap` carries the fibre
  section `SectionComponent.fiberSection (i ≫ p) e he t` to the fibre section of `p` defined by
  `e ≫ i`, and in particular carries `SectionComponent.fiberPoint (i ≫ p) e he t` to
  `SectionComponent.fiberPoint p (e ≫ i) _ t`.
- `isClosed_fiberPoint`: if `i ≫ p` is locally of finite type, the point of the fibre
  `(i ≫ p).fiber t` selected by the section is closed.
- `componentSet_subset_range`: let `i` be a closed immersion, `p` smooth of relative dimension
  `n`, and every residue fibre of `i ≫ p` smooth of relative dimension `n`. Then
  `SectionComponent.componentSet p (e ≫ i) _` lies in the range of `i`. This set is the union,
  over `t : T`, of the connected components of the fibres `p.fiber t` through the section
  points.
- `exists_smooth_open_of_closedImmersion`: let `T` be reduced, `p : Z ⟶ T` smooth of relative
  dimension `n`, quasi-compact and quasi-separated, and `i : Y ⟶ Z` a closed immersion. Let
  `e : T ⟶ Y` satisfy `e ≫ i ≫ p = 𝟙 T`, and assume every residue fibre
  `(i ≫ p).fiberToSpecResidueField t` is `SmoothOfRelativeDimension n`. Then there is an open
  `W` of `Y` containing the range of `e` such that `W.ι ≫ i ≫ p` is smooth.

## Provenance

These are internal lemmas for this proof, with derived names. The argument does not follow
SGA 3 VI_B 4.4, which goes through flatness (EGA IV₃ 15.6.7). Instead it combines three
Library results. The first is the openness of the union of fibre components meeting a section
(`SectionComponent.flatFinitePresentationOpenness`, a form of EGA IV₃ 15.6.5). The second is
the reducedness of schemes smooth over a reduced base
(`Langlands.AlgebraicGeometry.SmoothReducedBase.isReduced_of_smooth_of_isReduced`). The third
is the dimension of stalks at closed points of smooth schemes over a field
(`Langlands.AlgebraicGeometry.fieldSmoothClosedPointStalkDimension`).

## Proofs

`injective_of_surjective_of_ringKrullDim_eq`. If `f a = 0` with `a ≠ 0`, then `a` is a
non-zero-divisor of the domain `A`. Mathlib's `ringKrullDim_succ_le_of_surjective` then gives
`ringKrullDim B + 1 ≤ ringKrullDim A`, that is `n + 1 ≤ n`, a contradiction.

`connectedComponent_subset_range_of_closedImmersion`. `X` is smooth over `k`, hence locally
Noetherian, and all its stalks are domains. The latter comes from the Library theorem
`AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk`, applied over
`Spec k`, whose ring of global sections is a field. The point `j x'` is closed because `j` is
a closed map. By `fieldSmoothClosedPointStalkDimension`, both stalks `O_{X, j x'}` and
`O_{X', x'}` have Krull dimension `n`. The stalk map of the closed immersion `j` at `x'` is
surjective (`Scheme.Hom.stalkMap_surjective`), so it is injective by the previous lemma, hence
an isomorphism. Every generization `y` of `j x'` lies in the image of
`Spec O_{X, j x'} → X` (`Scheme.range_fromSpecStalk`). Since `Spec` of the stalk map is
surjective, `y` is the image of a point of `Spec O_{X', x'}`, so `y` lies in the range of `j`
(`Scheme.SpecMap_stalkMap_fromSpecStalk`). Next, `X` is locally Noetherian with domain stalks,
so the irreducible component of `j x'` is open. This is the Library theorem
`AlgebraicGeometry.isOpen_irreducibleComponent_of_isDomain_stalk`. It is also closed, hence
clopen, so it contains the connected component of `j x'`. The generic point of this
irreducible component generizes `j x'`, so it lies in the closed set `range j`. Therefore the
whole component lies in `range j`.

`fiberMap` and its lemmas. `fiberMap` is `pullback.map` with `i` on the first factor and
identities elsewhere. It is a closed immersion because closed immersions are stable under the
induced map of pullbacks (`MorphismProperty.pullbackMap`). `fiberSection_comp_fiberMap` is
checked on the two pullback projections using the `fiberSection` simp lemmas, and
`fiberMap_fiberPoint` evaluates it at the closed point of `Spec κ(t)`.

`isClosed_fiberPoint`. The fibre section `σ : Spec κ(t) → (i ≫ p).fiber t` is a section of
the projection, so `σ` is locally of finite type (`locallyOfFiniteType_of_comp`). A morphism
locally of finite type maps closed points to closed points
(`Scheme.Hom.closePoints_subset_preimage_closedPoints`), and the closed point of `Spec κ(t)`
is closed.

`componentSet_subset_range`. Take a point of `componentSet`, given by `t : T` and a point `z`
of `p.fiber t` in the connected component of the section point. The fibre of `p` is smooth of
relative dimension `n` over `κ(t)` by base change (`MorphismProperty.pullback_snd`). The fibre
of `i ≫ p` is smooth of relative dimension `n` by hypothesis, and `fiberMap p i t` is a closed
immersion. Moreover `fiberMap` carries the section point of `(i ≫ p).fiber t` to the section
point of `p.fiber t`, and that point is closed by `isClosed_fiberPoint`.
`connectedComponent_subset_range_of_closedImmersion` therefore gives `z = fiberMap p i t w`.
Hence the image of `z` in `Z` is `i` applied to the image of `w` in `Y`.

`exists_smooth_open_of_closedImmersion`. `p` is smooth, hence flat, locally of finite
presentation and geometrically reduced (Library theorem
`Langlands.AlgebraicGeometry.smoothGeometricallyReduced`). Together with quasi-compactness and
quasi-separatedness, the Library theorem `SectionComponent.flatFinitePresentationOpenness` shows
that `U0 = componentSet p (e ≫ i) _` is open in `Z`. By `componentSet_subset_range`,
`U0 ⊆ range i`. Take `W = i ⁻¹ᵁ U0`. It contains the range of `e` because every section point
lies in `componentSet` (`SectionComponent.section_mem_componentSet`). The open subscheme `U0`
is smooth over the reduced scheme `T`, hence reduced (`isReduced_of_smooth_of_isReduced`). The
restriction `i ∣_ U0 : W → U0` is a closed immersion and surjective because `U0 ⊆ range i`.
A surjective closed immersion onto a reduced scheme is an isomorphism (Mathlib's
`isIso_of_isClosedImmersion_of_surjective`). Thus `W.ι ≫ i ≫ p = (i ∣_ U0) ≫ U0.ι ≫ p`
(`morphismRestrict_ι`) is an isomorphism followed by an open immersion and the smooth `p`, so
it is smooth.

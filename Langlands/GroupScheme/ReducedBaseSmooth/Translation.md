# Smoothness spreads from the unit section by translation

Author: Worker 9.

Helper module for the proof of
`Langlands.GroupScheme.ReducedBaseConnectedFibreSmoothStatement` (SGA 3, Exposé VI_B,
Corollaire 4.4, reduced locally Noetherian base, connected fibres). It reduces smoothness of
a group scheme `H → S` to smoothness at the points of the unit section: if every fibre is
smooth and connected, then translating the smooth locus covers all of `H`.

All declarations are in the namespace `Langlands.GroupScheme.ReducedBaseSmooth`, and all
schemes lie in one universe `u`. Here `H : GroupScheme S` is a group object in `Over S`,
`H.X` is its underlying object over `S`, and `H.X.hom : H.X.left ⟶ S` is its structure
morphism. `μ[H.X]` is the multiplication and `η[H.X]` the unit section.

## Declarations

- `tensorHom_comp_mul_eq`: for a morphism `i : P ⟶ H.X` in `Over S`,
  `(i ⊗ₘ i) ≫ μ[H.X] = (𝟙 P ⊗ₘ i) ≫ (DominantHomFlat.shearLeft i).hom ≫ snd P H.X`. In
  points: `(a, b) ↦ i(a)·i(b)` is the map `(a, g) ↦ (a, i(a)·g)` (an isomorphism of
  `P ×_S H`), followed by the second projection, precomposed with `1 × i`.
- `smooth_tensorHom_comp_mul`: if `P → S` is smooth and `i.left` is an open immersion, then
  the underlying morphism of `(i ⊗ₘ i) ≫ μ[H.X]`, from `P ×_S P` to `H`, is smooth.
- `range_tensorHom_comp_mul_eq_univ`: suppose every residue fibre
  `H.X.hom.fiberToSpecResidueField s` is smooth and every fibre `H.X.hom.fiber s` is a
  connected space. If `i.left` is an open immersion whose range contains the range of the
  unit section, then the map `P ×_S P → H`, `(a, b) ↦ i(a)·i(b)`, is surjective (its range
  is `Set.univ`).
- `smooth_of_smooth_comp_of_surjective`: let `p : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of
  schemes with `p` smooth and surjective, `p ≫ g` smooth, `g` locally of finite presentation
  and `Y` locally Noetherian. Then `g` is smooth. No quasi-compactness of `p` is assumed.
- `smoothLocusOver H : Over S` is the open subscheme `H.X.hom.smoothLocus` of `H.X.left`,
  viewed over `S`. `smoothLocusInclusion H` is its inclusion into `H.X`. Two instances record
  that this inclusion is an open immersion and that `smoothLocusOver H` is smooth over `S`.
- `smooth_of_range_unit_subset_smoothLocus`: let `S` be locally Noetherian and `H → S`
  locally of finite type. Assume every residue fibre of `H.X.hom` is smooth and every fibre is
  connected. If the range of the unit section `η[H.X].left` lies in the smooth locus
  `H.X.hom.smoothLocus`, then `H.X.hom` is smooth.

## Provenance

The route is internal to this proof and does not follow SGA 3. SGA 3 VI_B 4.4 obtains
flatness of `G → S` from EGA IV₃ 15.6.7 and then concludes with VI_B 3.10. This file only
uses a standard translation argument. For a smooth group `G` over a field and an open
neighbourhood `V` of the unit, every point of the identity component of `G` is a product of
two points of `V`. That fact enters
through the Library theorem
`Langlands.GroupScheme.RelativeIdentityComponent.identitySet_subset_range_fieldOpenProduct`.
The statements here are internal helper lemmas; their names are derived.

## Proofs

`tensorHom_comp_mul_eq`. Rewrite with the Library lemma
`DominantHomFlat.shearLeft_hom_snd`, which describes the second component of the left shear
as `fst ≫ u` times `snd`, and with `MonObj.comp_mul`; then simplify the projections of a
tensor product of morphisms.

`smooth_tensorHom_comp_mul`. By `tensorHom_comp_mul_eq`, the underlying morphism is
`(𝟙 P ⊗ₘ i).left ≫ (shearLeft i).hom.left ≫ (snd P H.X).left`. The first map is an open
immersion: it is the map of pullbacks over `S` induced by `𝟙` and the open immersion `i.left`
(`MorphismProperty.pullbackMap`). The second is an isomorphism, and the third is the base
change of the smooth morphism `P → S` along `H → S`. Hence the composite is smooth.

`range_tensorHom_comp_mul_eq_univ`. Let `h` be a point of `H` over `s ∈ S`, and let
`b : Spec κ(s) ⟶ S` be the residue point. Base-change `H`, `P` and `i` along `b`; the new
group `H'` is smooth over `κ(s)` and connected, and `i'` is still an open immersion
(`MorphismProperty.of_isPullback` with `overPullback_isPullback`). The unit section factors
through `i` (`FiniteEtaleImage.liftOver`), so the unit point of `H'` lies in the range of `i'`.
Then `identitySet_subset_range_fieldOpenProduct` shows that the identity component of `H'`
lies in the range of the product map of `i'`. The identity component is all of `H'` because
`H'` is connected. The Library theorem
`RelativeIdentityComponent.range_baseChangedProduct` identifies the range of the base-changed
product with the inverse image, under `H' → H`, of the range of the original product. Applied
to the point `H.X.hom.asFiber h` of the fibre, which maps to `h`
(`Scheme.Hom.fiberι_asFiber`), this shows that `h` is a product.

`smooth_of_smooth_comp_of_surjective`. It suffices to show that the smooth locus of `g` is
everything (`Scheme.Hom.smoothLocus_eq_top_iff`). Given `y = p x`, choose an affine open
`W ∋ x`. Its image `V = p(W)` is open because smooth morphisms are open maps. The
restriction `q : W → V` of `p` is smooth (`IsZariskiLocalAtSource.resLE`) and surjective. It
is quasi-compact because `W` is affine and `V` is quasi-separated, being an open of a locally
Noetherian scheme (`quasiCompact_of_compactSpace`). The composite `q ≫ V.ι ≫ g` equals
`W.ι ≫ p ≫ g` and is smooth. The Library theorem
`AlgebraicGeometry.Smooth.of_comp_of_smooth_of_surjective_of_locallyOfFinitePresentation`
(smooth descent along a smooth, surjective, quasi-compact morphism) shows that `V.ι ≫ g` is
smooth. Therefore `V` lies in the smooth locus of `g` (`Scheme.Hom.preimage_smoothLocus_eq`),
and in particular `y` does.

`smooth_of_range_unit_subset_smoothLocus`. Let `i` be the inclusion of the smooth locus. `H` is
locally Noetherian, since it is locally of finite type over a locally Noetherian base. By
`smooth_tensorHom_comp_mul` the map `m : P ×_S P → H`, `(a, b) ↦ a·b`, is smooth. It is
surjective by `range_tensorHom_comp_mul_eq_univ`; its hypothesis is the assumption on the unit
section, via `Scheme.Opens.range_ι`. The composite `m ≫ H.X.hom` is the structure morphism of
`P ×_S P`, which is smooth. Local finite type over a locally Noetherian base gives local finite
presentation, so `smooth_of_smooth_comp_of_surjective` applies and `H.X.hom` is smooth.

# Closed normalizers of smooth connected subgroups over an affine base

This helper module of `Langlands.GroupScheme.smoothConnectedNormalizer`
proves the target over an affine base `Spec R`.

## Main result

`exists_normalizer_affine`: let `G` and `H` be group schemes over `Spec R`,
with `G` smooth and affine over `Spec R`. Let `i : H ⟶ G` be a closed subgroup
with `H` smooth and geometrically connected over `Spec R`. Then there are a
group scheme `N` over `Spec R` and a homomorphism `j : N ⟶ G` that is a closed
immersion, is locally of finite presentation, and represents the all-test
normalizer of `SubgroupFunctor.range i`. The hypotheses and conclusion are
those of `SmoothConnectedNormalizerStatement` with `S = Spec R`.

`connectedSpace_tensor_of_geometricallyConnected` is an auxiliary result: if
`Spec C → Spec R` is geometrically connected, then `Spec (K ⊗[R] C)` is
connected for every field `K` over `R`. The pushout square of rings gives a
pullback square of spectra.

## Proof

`G` is affine. The Library's `AffineCoordinates` identifies it with the group
scheme corepresented by its coordinate algebra `B`, and `coordinateHom i`
transports `i`. The Library's `exists_ideal_range` gives an ideal `I` of `B`
cutting out the range of this closed subgroup. The cut-out group scheme
`Spec (B ⧸ I)` and `H` represent the same subgroup functor, so they are
isomorphic (`IsRepresentedBy.isoOfIsRepresentedBy`).

The hypotheses on `H` transfer along this isomorphism:

- `B ⧸ I` is smooth over `R` (Library `smooth_groupScheme_iff`);
- `Spec (B ⧸ I) → Spec R` is geometrically connected, since geometric
  connectedness respects isomorphisms; hence every field fibre is connected;
- `B` is smooth over `R` (`AffineCoordinates.smooth_algebra`), in particular
  finitely presented, so the kernel `I` of the surjection `B → B ⧸ I` is
  finitely generated.

Then `CutOut` gives the ideal `smoothNormalizerIdeal` cutting out the
normalizer family, together with its finite generation. By the Library's
`affineSubgroups_normalizer`, this family is the coordinate form of the
normalizer of the range. The Library's
`isRepresentedBy_cutHom_affineSubgroups` then makes the closed subgroup scheme
`Spec (B ⧸ smoothNormalizerIdeal)` a representative.

The required `j` is this cut-out inclusion composed with the coordinate
isomorphism to `G`. It is a closed immersion. It is locally of finite
presentation, because `B → B ⧸ smoothNormalizerIdeal` has a finitely generated
kernel and is therefore of finite presentation (`HasRingHomProperty.Spec_iff`).
Representation is transported through the isomorphism by
`SubgroupFunctor.normalizer_range_eq_comap_of_iso` and
`IsRepresentedBy.comp_iso`.

## Provenance

This is Brian Conrad, *Reductive group schemes* (2014), Proposition 2.1.6
(subgroup case, printed and one-based PDF pp.61–63, source
`conrad-2014-reductive-group-schemes`), over an affine base. The assembly
through the Library's affine coordinate interfaces is internal to this proof.

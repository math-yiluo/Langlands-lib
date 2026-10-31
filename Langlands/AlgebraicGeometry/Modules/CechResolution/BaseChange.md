# Maps of sheafified Čech complexes over a morphism of schemes

This module constructs the actual map induced by a module-sheaf morphism
`a : M ⟶ (Scheme.Modules.pushforward g).obj N`, where `g : Y ⟶ X` is a
morphism of schemes in arbitrary universe `u`. For an affine morphism `g`
and an ordered affine cover `𝒰` of `X`, it produces a cochain map from
`cechComplex 𝒰 M` to the pushforward of the Čech complex of `N` on the
inverse-image cover, and proves the full augmentation square. Specializing
`a` to the pullback/pushforward adjunction unit gives the actual Čech
pullback map and its augmentation square.

The module is an internal construction from the sheafified Čech definitions
in `CechResolution.Basic` and `CechResolution.Complex`, the ordered-cover
definitions, Mathlib's affine-morphism API, and the published
`AcyclicResolution.mapResolutionAugmentation`. Worker 606 authored this
extension; Worker 958's Čech constructions supply its imported interface.
The construction below assumes no cohomological base-change theorem.

## Maps on open factors

For opens `W` of `X` and `W'` of `Y` with `W' ≤ g⁻¹ W`,
`sheafOnPushforward_le` proves that `W' ∩ g⁻¹ V` is contained in
`g⁻¹(W ∩ V)`. The notation in Lean expresses intersections as the image
of the corresponding open-immersion preimage. The map
`sheafOnPushforwardApp g a hW V` first applies `a` on `W ∩ V`, then
restricts the resulting section of `N` to `W' ∩ g⁻¹ V`.

`sheafOnPushforwardApp_naturality` follows from naturality of `a` and
composition of restriction maps. `sheafOnPushforwardApp_smul` checks
linearity for the actual structure-sheaf scalar action. Its proof uses
naturality of `g` on rings of sections, linearity of `a`, and the
restriction map's scalar compatibility. These two checks assemble the
module-sheaf morphism
`sheafOnPushforward : sheafOn M W ⟶ g_*(sheafOn N W')`.
`sheafOnPushforward_app` records its precise sections formula.

`unit_sheafOnPushforward` proves compatibility with the restriction units
`M ⟶ sheafOn M W` and `N ⟶ sheafOn N W'`.
`res_sheafOnPushforward` proves compatibility when both opens are shrunk.
Both proofs reduce to naturality of `a` and equality of the relevant
inclusion morphisms in the poset of opens.

## Ordered covers and differentials

Assume `[IsAffineHom g]`. `inverseImageCover g 𝒰` keeps the finite ordered
index type of `𝒰` and replaces each chart by its inverse image under `g`.
The affine-morphism hypothesis ensures these charts are affine.
`inverseImageCover_inter` identifies each finite chart intersection with
the inverse image of the original intersection; the associated containment
`inverseImageCover_inter_le` supplies the input for each factor map.

`cechTermPushforward g a 𝒰 p` is assembled from these factor maps and the
source finite-biproduct projections. The pushforward, as a right adjoint,
preserves the product underlying the finite biproduct. Its preserved
limit cone therefore supplies the required map, without identifying
different chosen biproduct objects. `cechTermPushforward_π` gives its
component at each strictly increasing tuple. The auxiliary
`pushforward_biproduct_hom_ext` proves that these pushed-forward
projections determine the map.

`cechTermPushforward_cechD` proves compatibility with the alternating
differentials. After composing with a projection, both sides become
finite sums indexed by deleted entries of the tuple. Additivity of
pushforward moves it through sums and integer multiples, and
`res_sheafOnPushforward` identifies each summand. The resulting cochain
map is `cechPushforward`; `cechPushforward_f` records its degreewise
components.

## Augmentations and the pullback unit

`augmentation_cechTermPushforward` proves the degree-zero square by
projection onto each factor and `unit_sheafOnPushforward`.
`cechAug_cechPushforward` promotes this identity to the full cochain
square

```text
cechAug 𝒰 M ≫ cechPushforward g a 𝒰
  = single₀.map a ≫ mapResolutionAugmentation (pushforward g)
      (cechAug (inverseImageCover g 𝒰) N).
```

Maps from the complex concentrated in degree zero are determined by
their zero component, so the proof reduces directly to the degree-zero
identity and the published component formula for mapped augmentations.

`cechPullback g 𝒰` specializes this cochain map to
`a = (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M` and
`N = (Scheme.Modules.pullback g).obj M`.
`cechAug_cechPullback` gives the same augmentation square for this actual
unit-induced map. These are compatible augmented complexes; the module
does not assert that their global-sections scalar comparison is an
isomorphism, or that the Čech terms are acyclic. Those require separate
geometric inputs.

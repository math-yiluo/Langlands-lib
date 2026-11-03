# Closed immersions and actual equivariant weight quotients: proof

This module proves the proposition
`Langlands.GroupScheme.PointedCoordinateWeights.ClosedImmersionPullbackStatement.{u}`
from the module `Langlands.GroupScheme.Rational.ClosedImmersionPullbackStatement`.
The statement pair is unchanged.

## Main theorem

`closedImmersionPullback : ClosedImmersionPullbackStatement.{u}` is
`closedImmersionPullback_of_decomposition` (below) applied to the published
split-torus decomposition `pointedCoordinateDecomposition :
PointedCoordinateDecompositionStatement.{u}`, imported from
`Langlands.GroupScheme.Rational.PointedCoordinateDecompositionProof`.

All declarations are in the namespace
`Langlands.GroupScheme.PointedCoordinateWeights`.

## Helper results

1. `eq_of_iSupIndep_of_le_of_iSup_eq_top` (pure lattice theory). In a complete
   modular lattice, let `M` be an independent family (`iSupIndep M`) and `N` a
   family with `N i ≤ M i` for every `i` and `⨆ i, N i = ⊤`. Then `N i = M i`
   for every `i`. Write `R` for the supremum of the `N j` with `j ≠ i`; it lies
   below the supremum of the `M j` with `j ≠ i`, so `M i ⊓ R = ⊥` by
   independence. `iSup_split_single` gives `N i ⊔ R = ⊤`, hence
   `M i = (N i ⊔ R) ⊓ M i`. The modular law (`sup_inf_assoc_of_le`, using
   `N i ≤ M i`) rewrites this as `N i ⊔ (R ⊓ M i) = N i ⊔ ⊥ = N i`.
2. `algSpec_map_pullback` is imported from the published module
   `Langlands.GroupScheme.Rational.DominantPullbackProof`. For affine `V` and
   `W` over `Spec k` and `f : V ⟶ W`, it states that the morphism `algSpec` of
   `pullback f`, composed with `coordinateIso W`, equals `coordinateIso V`
   composed with `f`.
3. `pullback_surjective_of_isClosedImmersion` (clause 1). If `f.left` is a
   closed immersion, `pullback f` is surjective. Let `ψ` be the underlying ring
   map of `pullback f`. Taking left components of helper 2 identifies
   `Spec.map ψ` with `f.left` conjugated by the isomorphisms
   `(coordinateIso V).hom.left` and `(coordinateIso W).inv.left`. So
   `Spec.map ψ` is a closed immersion between affine schemes, and
   `IsClosedImmersion.isAffine_surjective_of_isAffine` makes its map on global
   sections surjective. `Scheme.ΓSpecIso_naturality` writes `ψ` as that
   global-sections map conjugated by the ring isomorphisms `ΓSpecIso`, so `ψ`
   is surjective.
4. `map_weightSpace_eq_of_isInternal` (clause 3 from decomposition data).
   Suppose `f` is pointed equivariant from `a` to `b` and `pullback f` is
   surjective. Suppose also that the weight spaces of `a` are independent and
   those of `b` span `Coord W`. Then the image of `weightSpace b χ` under
   `pullback f` equals `weightSpace a χ` for every character `χ`. Apply
   helper 1 in the lattice of `k`-submodules of `Coord V`, with `M = weightSpace a`
   and `N χ` the image of `weightSpace b χ`.
   - `N χ ≤ M χ` is the published `pullback_mem_weightSpace`.
   - `⨆ χ, N χ` is the image of `⨆ χ, weightSpace b χ = ⊤` (`Submodule.map_iSup`),
     which is the range of `pullback f`, hence `⊤` by surjectivity.
5. `mem_augmentation_of_pullback`. If `pullback f y` lies in the augmentation
   of `a`, then `y` lies in the augmentation of `b`. The published
   `pullback_origin` gives `coordinateOrigin a ∘ pullback f = coordinateOrigin b`.

## Conditional theorem

`closedImmersionPullback_of_decomposition
(hdec : PointedCoordinateDecompositionStatement.{u}) :
ClosedImmersionPullbackStatement.{u}`.

Fix `k`, a split torus `S` (with `hS : IsSplitTorus S.toGrp`), affine pointed
`S`-schemes `V` and `W` with actions `a` and `b`, and a pointed equivariant
`f` whose underlying morphism is a closed immersion. The split-torus hypothesis
is used only through `hdec`.

- Clause 1 is helper 3.
- Clause 3 is helper 4. Independence of the weight spaces of `a` comes from
  `DirectSum.IsInternal.submodule_iSupIndep` applied to the first conjunct of
  `hdec` for `V`. Spanning for `b` comes from
  `DirectSum.IsInternal.submodule_iSup_eq_top` applied to the first conjunct of
  `hdec` for `W`. Only the coordinate decompositions are used; the
  augmentation decompositions (second conjuncts) are not needed.
- Clause 4 (`HasWeightwiseLifts`). Let `z` be in the augmentation of `a` and
  in `weightSpace a χ`. By clause 3 there is `y ∈ weightSpace b χ` with
  `pullback f y = z`. By helper 5, `y` lies in the augmentation of `b`. So
  `⟨y, _⟩` is a lift of `z` in `augmentationWeightSpace b χ`.
- Clause 2 (surjectivity of `augmentationPullback`). Lift `z` by clause 1 and
  apply helper 5 in the same way.
- Clause 5 (support containment) is the published
  `support_subset_of_weightwise_lifts` applied to clause 4.

## Provenance

The target is derived from Conrad–Gabber–Prasad, *Pseudo-reductive Groups*,
second edition (2015), §3.3, printed pp.107–108 (PDF pp.133–134), registered
as `conrad-gabber-prasad-2015-pseudo-reductive`. The source uses without
comment that an `S`-stable closed subscheme through the identity receives
every weight of its augmentation ideal from the ambient augmentation ideal.
Examples are the equivariant quotient step in Example 3.3.2 and the
containments `V, V' ⊆ VV'` in the proof of Lemma 3.3.4. The standard reason
is that an equivariant surjection of coordinate rings, both of which decompose
into weight spaces, is surjective on each weight space. Helpers 1 and 4 make
this precise. Helpers 3 and 5, and the imported helper 2, are routine translations between the actual
coordinate presentations of the Library and Mathlib's closed-immersion API.

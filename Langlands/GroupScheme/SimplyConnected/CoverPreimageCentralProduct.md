# The multiplication map of a central torus and the derived subgroup

Author: Worker 1413.

Module `Langlands.GroupScheme.SimplyConnected.CoverPreimageCentralProduct`,
namespace `Langlands.GroupScheme.CoverPreimage`. Internal helpers for the
reduction
[`SplitTorusCentralizerCoverPreimageReduction`](SplitTorusCentralizerCoverPreimageReduction.md).
The helpers derive the properties of the multiplication map `Z × D ⟶ G`
needed there from the conclusion of the published
`ReductiveCentralDerivedProductStatement`, which is an epimorphism of
schemes. `IsCentralFppfCover` is defined in
[`CoverPreimageToolkit`](CoverPreimageToolkit.md).

## Over an arbitrary base

- `centralProduct i d hic : Z × D ⟶ G` is the published `prodHom i d`. Here
  `i : Z ⟶ G` is central (`hic : IsCentral i`), `Z` is commutative and
  `d : D ⟶ G` is arbitrary. On points it is `(z, y) ↦ i(z) d(y)`
  (`comp_centralProduct`). Its underlying morphism is the published
  `subgroupProductMap i d` (`centralProduct_hom`).
- `centralProduct_kernel_central`: if `d` is monomorphic, every point killed
  by `centralProduct i d hic` is central in `Z × D`. If `i(z) d(y) = 1`, then
  `d(y) = i(z)⁻¹` is central in `G`, so `y` is central in `D`, and `Z` is
  commutative.
- `isCentral_of_comp_mono`: if `iM ≫ j = i` with `j` monomorphic and `i`
  central, then `iM` is central.
- `restrictedProduct d j iM hic` is the central product of `iM : Z ⟶ M` with
  the second projection `subgroupIntersection d j ⟶ M` of the intersection
  `D ×_G M`.
- `isCentralFppfCover_restrictedProduct`. Let `d` and `j : M ⟶ G` be
  monomorphic and `iM ≫ j = i`. If `centralProduct i d hic` is a central
  fppf cover, then so is the restricted product `Z × (D ×_G M) ⟶ M`. The proof
  shows that the square formed with `Z × (D ×_G M) ⟶ Z × D` (the whiskered
  first projection) and `j` is cartesian. The published
  `SubgroupFunctor.IsRepresentedBy.isPullback_of_comap_eq` reduces this to an
  equality of subgroup functors on all test schemes. A point `(z, y)` of
  `Z × D` with `i(z) d(y) = j(m)` comes from the intersection point
  `(y, iM(z)⁻¹ m)`. Then `IsCentralFppfCover.of_isPullback` applies.

## Over a field

- `derivedSubgroup_smooth_connected_affine`: the derived subgroup of a
  connected reductive group is smooth, connected and affine. This comes from
  the published `derivedSubgroupSmoothness` and `derivedSubgroupConnectedness`.
- `isCentralFppfCover_centralProduct`. Let `G` be connected reductive with
  derived subgroup `d`, and let `i : Z ⟶ G` be a central closed torus with
  `Epi (subgroupProductMap i d)`. Then `centralProduct i d hic` is a central
  fppf cover.
  - *Fppf.* `Z × D` is smooth, connected and affine (published
    `smoothConnectedAffineGeometry`). The published `HomImage.exists_image`
    factors the product map through a closed subgroup `I ⊆ G` by a flat,
    surjective, quasi-compact homomorphism locally of finite presentation.
    The closed inclusion `I ⟶ G` is then an epimorphism, hence an
    isomorphism (published `isIso_of_isClosedImmersion_of_epi_over`).
  - *Centrality.* The kernel is central by `centralProduct_kernel_central`.
  - *Torsion.* The published `derivedCentralIntersectionFiniteness` gives a
    finite closed subgroup `c : C ⟶ D` whose range is the inverse image of
    the centre of `G`. It is commutative (published `IsCentral.isCommMonObj`),
    so some `N > 0` kills it (published `exists_pow_eq_one_of_isFinite`).
    If `(z, y)` is killed by the product map, then `d(y)` is central, so `y`
    is a point of `C` and `y^N = 1`. Then `i(z^N) = d(y^N)⁻¹ = 1`, so
    `z^N = 1`.

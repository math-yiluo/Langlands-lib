# AF representations over a finite disjoint open cover of the base

Author: Worker 5067.

Helper module for the proof of
`Langlands.AlgebraicGeometry.Picard.FiniteTypeAbelianPicardSheafSchemeReductionStatement`
(Task 5600). All declarations are in namespace
`Langlands.AlgebraicGeometry.AlgebraicSpace.LocalRepresentation`, the namespace of the
Library's local representations, and extend that Library material. "AF" abbreviates the
Library property `PointTopology.HasFiniteAffineNeighborhoods X`: every finite set of
points of the scheme `X` lies in one affine open.

## Declarations

- `chart_relative j H e P hj`. Data: a morphism `j : U ⟶ B`, `H : Over U` and a
  representation `e : (schemeYoneda U).obj H ≅ (Over.map j).op ⋙ F` of the restriction of
  a presheaf `F` on `Over B`. If `P` is a morphism property of schemes stable under base
  change and `P j` holds, then the Library global chart
  `chart j H e : (schemeYoneda B).obj ((Over.map j).obj H) ⟶ F` has `P` relatively. That
  is, it satisfies `(P.inverseImage (Over.forget B)).relative (schemeYoneda B)`, the
  representable-morphism form of `P` used by `AlgebraicSpace.IsFinite`,
  `AlgebraicSpace.IsSurjective` and the like. The Library already proves this for
  `P = IsOpenImmersion` (`chart_isOpenImmersion`), and the proof is the same. The chart is
  the Library isomorphism `chartProductIso j H e` followed by the projection
  `extProd F (Over.mk j) ⟶ F`. That projection has `P` relatively by the Library lemma
  `extProd.relative_fst`, and relative properties are invariant under precomposition with
  isomorphisms.
- `hasFiniteAffineNeighborhoods_of_disjoint_cover f hcov hdisj hY`. Let `X` be a scheme
  with finitely many open immersions `f k : Y k ⟶ X`, jointly surjective (`hcov`), with
  pairwise disjoint images (`hdisj`), and each `Y k` AF (`hY`). Then `X` is AF. Proof:
  for a finite set `s ⊆ X`, each preimage `(f k)⁻¹ s` is finite, so it lies in an affine
  open `W k` of `Y k`. The images `O k = f k '' W k` are affine opens of `X`. They are
  pairwise disjoint because the images of the `f k` are. Mathlib's
  `IsAffineOpen.iSup_of_disjoint` shows that a finite union of pairwise disjoint affine
  opens is affine. This union contains `s`.
- `exists_representation_of_disjoint_cover hF 𝒰 hdisj H hH e`. Let `F` be an fppf sheaf
  on `Over B` and `𝒰` an open cover of `B` with finite index set whose members have
  pairwise disjoint images. Suppose that over each member `𝒰.X i` the restriction
  `(Over.map (𝒰.f i)).op ⋙ F` is represented by `H i : Over (𝒰.X i)` with `(H i).left`
  AF. Then `F` is represented by some `V : Over B` with `V.left` AF. Proof: the Library
  theorem `LocalRepresentation.exists_representation` glues the local representatives
  to `V` with `(schemeYoneda B).obj V ≅ F`. The pullbacks `V ×_B 𝒰.X i → V` are open
  immersions. They cover `V`, by `Scheme.Pullback.exists_preimage_pullback`. Their images
  are pairwise disjoint, because their images in `B` lie in the disjoint `𝒰.f i`-images.
  Each pullback is isomorphic to `(H i).left`, by the Library's `localRepresentativeIso`.
  It is therefore AF by `FinitePinching.hasFiniteAffineNeighborhoods_of_iso`. The previous
  lemma then shows that `V.left` is AF.

## Use

The reduction proof applies `exists_representation_of_disjoint_cover` to the sigma open
cover of a finite disjoint union of normalized components. It applies `chart_relative`
with `P = IsFinite` and `P = Surjective` to the finite surjective normalization cover.

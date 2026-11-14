# From `Res_{(I → L)/k} 𝔾ₘ` to the Weil restriction of a split `L`-torus

Author: Worker 33.

Let `L / k` be a field extension, `I` a finite index type, `G` a group scheme
over `Spec L` and `σ : G ≅ 𝔾ₘ^I` an isomorphism with the Library's split torus
`splitTorus (Spec L) I`. This module builds a homomorphism of `k`-group
schemes

`splitWeilHom k L I G σ : Res_{(I → L)/k} 𝔾ₘ ⟶ Res_{L/k} G`,

from the Library's `WeilGm.groupScheme k (I → L)` (module
`Langlands.GroupScheme.Torus.WeilRestriction`) to the Library's
`AffineWeil.groupScheme k L G` (module
`Langlands.GroupScheme.AffineWeilRestriction`). It computes the map on rational
points and describes the character-valuation kernel of `G(L)` in split
coordinates. All declarations are in the namespace
`Langlands.GroupScheme.WeilGm`; all types lie in one universe `u`.

## Provenance

This is internal supporting material for the proof of
`UnramifiedTorusIwahoriConnectedImageStatement`. Mathematically,
`(I → L) ⊗[k] T ≃ ∏_{i ∈ I} L ⊗[k] T` identifies `Res_{(I → L)/k} 𝔾ₘ` with
`Res_{L/k} 𝔾ₘ^I`, and `σ⁻¹` identifies that with `Res_{L/k} G`. These are
the identifications used, without comment, when Kaletha–Prasad (source ID
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`) write the
split torus `T_L` as `𝔾ₘ^I` in Lemma B.3.1 and the proof of Corollary B.8.7
(printed pp. 657, 683 / PDF pp. 688, 714). The module only constructs the
homomorphism and computes it; it does not prove that it is an isomorphism.

## Construction

- `splitCoord k L I T i : (I → L) ⊗[k] T →ₐ[k] L ⊗[k] T` is the `i`-th
  coordinate, `ev_i ⊗ id`. `splitCoord_tmul` evaluates it on pure tensors;
  `splitCoord_naturality` states that it commutes with a change
  `T → T'` of the test algebra; `rid_splitCoord` states that for `T = k` it is
  the `i`-th coordinate of `(I → L) ⊗[k] k ≃ (I → L)`.
- `algSpec_map_comp_algebraPointsEquiv_symm`: precomposing the split-torus
  point with unit coordinates `t` by `Spec` of an `L`-algebra map `f` gives the
  point with coordinates `f(t i)`. This is a restatement of the Library's
  `splitTorus.algebraPointsEquiv_naturality`.
- `splitWeilPointHom k L I G σ T`, for a commutative `k`-algebra `T`, sends a
  unit `w` of `(I → L) ⊗[k] T` to the point of `G` over the `L`-algebra
  `L ⊗[k] T` whose split coordinates are the units `splitCoord i w`. It is the
  split-torus point with these coordinates (inverse of
  `splitTorus.algebraPointsEquiv`) composed with `σ⁻¹`
  (`splitWeilPointHom_apply`). It is a group homomorphism.
- `splitWeilPointHom_naturality`: it commutes with a change of the test
  algebra; the proof combines `splitTorus.algebraPointsEquiv_naturality` with
  `splitCoord_naturality`.
- `splitWeilNat k L I G σ` is the resulting natural transformation from the
  functor `WeilGm.functor k (I → L)` (points `((I → L) ⊗[k] T)ˣ`) to
  `AffineWeil.pointFunctor k L G` (points `G(L ⊗[k] T)`).
- `splitWeilHom k L I G σ` is the induced homomorphism of corepresented group
  schemes, `Corepresented.groupSchemeMap` applied to the Library's
  corepresentations `corepresentableBy k (I → L)` and
  `AffineWeil.corepresentableBy k L G`. It requires `L` finite over `k`, `G`
  affine and `G → Spec L` locally of finite type, as `AffineWeil.groupScheme`
  does.

## Points

- `splitWeilHom_affinePoints'` and `splitWeilHom_affinePoints`: on points with
  values in an affine test algebra `T`, followed by the Library comparison
  `AffineWeil.pointsEquiv k L G T`, the homomorphism is `splitWeilPointHom`
  applied to the unit given by `affineUnitsEquiv`. This is the Library's
  `Corepresented.groupSchemeMap_affinePoints`. The two statements need
  `maxRecDepth 20000` for elaboration.
- `basePointsEquiv_splitWeilHom`: for a rational point `y` of
  `Res_{(I → L)/k} 𝔾ₘ`, the Library's base-point comparison
  `AffineWeil.basePointsEquiv k L G` of its image is the split-torus point over
  `L` whose `i`-th coordinate is the `i`-th coordinate of the unit
  `rationalUnitsEquiv k (I → L) y ∈ (I → L)ˣ`, composed with `σ⁻¹`. The proof
  unfolds `basePointsEquiv` into `pointsEquiv` and the tensor-unit comparison,
  then uses `splitWeilHom_affinePoints`,
  `algSpec_map_comp_algebraPointsEquiv_symm` and `rid_splitCoord`.
- `rationalCoeffEquiv_symm_basePointsEquiv_splitWeilHom` restates this as a
  rational point of `G`: it is `rationalPoints.map σ.inv` of the split-torus
  rational point (`splitTorus.affinePointsEquiv I (𝟙 _)`) with the same
  coordinates. The translation between the two point models is the Library's
  `IntegralModel.SplitTorusClosure.rationalCoeffEquiv_symm_algebraPointsEquiv_symm`.

## Character-valuation kernel

Here `v` is any valuation on `L` with values in a linearly ordered commutative
group with zero, and `characterValuationKernel v G` is the Library's subgroup
of rational points on which every rational character has valuation one
(module `Langlands.Geometry.Building.KPZeroSubgroups`).

- `mem_characterValuationKernel_iff_of_iso`: a rational point `x` of `G` lies
  in `characterValuationKernel v G` exactly when every split coordinate of
  `σ(x)` has valuation one. The Library's `mem_split_characterValuationKernel`
  gives this for the split torus itself. The two directions transport it along
  `σ` and `σ⁻¹` with `map_characterValuationKernel_le`.
- `map_inv_mem_characterValuationKernel_iff`: the image under `σ⁻¹` of the
  split-torus rational point with coordinates `t : I → Lˣ` lies in the kernel
  exactly when every `t i` has valuation one.

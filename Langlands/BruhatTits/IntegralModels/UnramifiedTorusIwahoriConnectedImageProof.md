# Proof: the torus Iwahori subgroup is the image of a connected smooth model

Authors: Worker 33, with Worker 340 (module
`Langlands.GroupScheme.Torus.WeilRestrictionIntegralModel`).

The theorem
`Langlands.BruhatTits.IntegralModels.unramifiedTorusIwahoriConnectedImage`
proves `UnramifiedTorusIwahoriConnectedImageStatement.{u}` at an arbitrary
universe `u`. Its auxiliary declarations are in the namespace
`Langlands.BruhatTits.IntegralModels.ConnectedImage`.

## Source and witness

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), source ID
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`. Definition
2.5.13 (printed p. 90 / PDF p. 121) defines `T(K)^0` as the image of `T(L)^b`
under the norm. Lemma B.3.1 (printed p. 657 / PDF p. 688) states that
`R_{o_ℓ/o} 𝔾ₘ` is smooth with (geometrically) connected special fibre and that
its `O`-points are the maximal bounded subgroup. The proof of Corollary B.8.7
(printed p. 683 / PDF p. 714) takes `S = R_{L/K}(T_L)` with the norm `S → T`.

The proof follows this route with one change of presentation. Write
`K = inertiaFixedField F`, `O = fixedFieldIntegers F` and `O_L` for the
valuation ring of `intermediateValuation F L`. The split hypothesis gives a
finite type `I` and an isomorphism `σ : T_L ≅ 𝔾ₘ^I`. The witness is

- `S = Res_{(I → L)/K} 𝔾ₘ` (`WeilGm.groupScheme K (I → L)`). Through `σ` it is
  the source's `R_{L/K}(T_L) ≅ R_{L/K}(𝔾ₘ^I)`, written as a Weil restriction of
  `𝔾ₘ` along the product algebra `I → L`;
- `W = Res_{(I → O_L)/O} 𝔾ₘ`, the source's `R_{o_L/o}(𝔾ₘ^I)`;
- `n = splitWeilHom ≫ GaloisNorm.norm`: the map
  `Res_{(I → L)/K} 𝔾ₘ ⟶ Res_{L/K} T_L` given by split coordinates and `σ⁻¹`,
  followed by the Library's algebraic norm `Res_{L/K} T_L ⟶ T`.

## Supporting modules

- `Langlands.GroupScheme.Torus.WeilRestrictionGeometricallyConnected`
  (Worker 33): `WeilGm.geometricallyConnected A B`, every fibre of
  `Res_{B/A} 𝔾ₘ` over a field is connected, for `B` finite projective over a
  commutative ring `A`.
- `Langlands.BruhatTits.IntegralModels.ConnectedImage.Integers` (Worker 33):
  `O_L` is the integral closure of `O` in `L`, finite and free over `O`;
  `piTensorEquiv F L I : K ⊗[O] (I → O_L) ≃ₐ[K] (I → L)`; units of `O_L` are
  the elements of valuation one.
- `Langlands.GroupScheme.Torus.WeilRestrictionSplitNorm` (Worker 33):
  `splitWeilHom`, its value on rational points, and the character-valuation
  kernel in split coordinates.
- `Langlands.GroupScheme.Torus.WeilRestrictionIntegralModel` (Worker 340):
  `WeilGm.integralModel R K B₀ B e`, the model `Res_{B₀/R} 𝔾ₘ` of
  `Res_{B/K} 𝔾ₘ` for `e : K ⊗[R] B₀ ≃ₐ[K] B`; its smoothness
  `WeilGm.integralModel_isSmooth`; and
  `WeilGm.mem_integralModel_integralPoints_iff`, which identifies its integral
  points with the units of `B` coming from units of `B₀`.

## Declarations of this module

- `ConnectedImage.model F L I` is
  `WeilGm.integralModel O K (I → O_L) (I → L) (piTensorEquiv F L I)`. The
  module `I → O_L` is projective over `O` because it is free (local instance
  `piIntegersProjective`).
- `mem_model_integralPoints_iff`: a rational point `y` of `S` is an integral
  point of the model exactly when every coordinate of the unit
  `rationalUnitsEquiv K (I → L) y ∈ (I → L)ˣ` has valuation one. By
  `mem_integralModel_integralPoints_iff`, `y` is integral exactly when this
  unit is the image of a unit `u` of `I → O_L`. Since
  `piTensorEquiv (1 ⊗ u) = u` coordinatewise, the forward direction is
  `isUnit_integers_iff`. Conversely, coordinates of valuation one lie in `O_L`
  and are units there.
- `normMap F L I T σ := splitWeilHom K L I T_L σ ≫ GaloisNorm.norm K L T`. The
  instance arguments `IsAffine T_L` and `LocallyOfFiniteType (T_L → Spec L)`,
  needed by `AffineWeil.groupScheme`, are section variables here.
- `splitPoint F L I T σ y` is the point of `T(L)` given by `σ⁻¹` of the
  split-torus point whose coordinates are the coordinates of
  `rationalUnitsEquiv K (I → L) y`.
- `map_normMap`: `rationalPoints.map (normMap …) y` is
  `rationalNorm K L T (splitPoint … y)`. The map on rational points of a
  composite is the composite. For the norm, the Library's
  `GaloisNorm.norm_rationalPoints` states
  `map norm (rationalPointsEquiv x) = rationalNorm x`. Unfolding
  `GaloisNorm.rationalPointsEquiv` reduces the claim to
  `rationalCoeffEquiv_symm_basePointsEquiv_splitWeilHom`.
- `mem_characterValuationKernel_iff_exists`: a point `x` of `T(L)` lies in
  the character-valuation kernel for `intermediateValuation F L` exactly when
  `x = splitPoint y` for an integral point `y` of the model. Forward: by
  `mem_characterValuationKernel_iff_of_iso`, the split coordinates of `σ(x)`
  have valuation one. Take `y` the rational point of `S` whose unit is the
  family of these coordinates; it is integral by
  `mem_model_integralPoints_iff`, and `splitPoint y = σ⁻¹(σ(x)) = x`.
  Backward: `map_inv_mem_characterValuationKernel_iff` together with
  `mem_model_integralPoints_iff`.
- `map_model_integralPoints`: the image of the integral points of the model
  under `rationalPoints.map (normMap …)` is
  `torusNormIwahori K L (intermediateValuation F L) T`. By
  `mem_torusNormIwahori`, the right side consists of the rational norms of
  points in the character-valuation kernel of `T_L`. The two inclusions follow
  from `map_normMap` and `mem_characterValuationKernel_iff_exists`.

## The main theorem

`unramifiedTorusIwahoriConnectedImage` introduces `F`, `T`, `L` and the split
hypothesis, and obtains `I` (finite, with a chosen `Fintype` structure) and
`σ`. From `IsSplitTorus` it derives that `T_L → Spec L` is affine
(`IsSplitTorus.isAffineHom`), hence that `T_L` is an affine scheme, and that
it is smooth (`IsSplitTorus.smooth`), hence locally of finite type. It then
supplies the witness `S`, `W = model F L I` and `n = normMap F L I T σ`:

- `W.IsSmooth` is `WeilGm.integralModel_isSmooth`;
- `W.HasGeometricallyConnectedFibres` is
  `WeilGm.geometricallyConnected O (I → O_L)`, since `I → O_L` is finite and
  projective over `O`;
- the image equality is `map_model_integralPoints`.

The proof uses `maxHeartbeats 800000` and `synthInstance.maxHeartbeats 100000`.

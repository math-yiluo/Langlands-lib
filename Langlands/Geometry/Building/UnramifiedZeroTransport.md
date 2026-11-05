# Transport of the data for `H(K)^0` along automorphisms

Helper module for the Iwahori–Weyl exact sequence. It provides the transport step in the proof
of Kaletha–Prasad, Lemma 2.6.24. That step is: conjugation carries the subgroup `M(k)^0` defined
by one set of choices to the subgroup defined by the conjugated choices. Combined with the
independence of the choices, it shows that `M(k)^0` is preserved.

## Contents

* `Langlands.GroupScheme.rationalPoints.map_comp_apply`: the map on rational points induced by
  `f ≫ g` is the composite of the induced maps.
* `Langlands.GroupScheme.GaloisPointComparison.rationalExtend_map`: extending scalars
  `G(k) → G(L)` commutes with a homomorphism `f : G ⟶ H`, that is
  `rationalExtend (f x) = f_L (rationalExtend x)`, where `f_L` is the base change of `f`. The
  proof passes to the coefficient-point descriptions through `baseChangeCoeffEquiv` and
  `rationalCoeffEquiv`. There it is the naturality `affinePointsTarget_naturality` of
  coefficient extension with respect to group-scheme homomorphisms.
* `Langlands.Geometry.Building.UnramifiedZeroDatum.transport` (definition): for data
  `E : UnramifiedZeroDatum F H` of KP Definition 2.6.23(1) and an automorphism `e : H ≅ H`, the
  transported data keep the torus `T`, the splitting field `L` and the simply connected cover
  `π : C → D`. They replace the torus inclusion `i` by `i ≫ e` and the derived-subgroup
  inclusion `d` by `d ≫ e`. Validity uses the published transport lemmas
  `IsMaximalTorus.comp_iso`, `IsMaximalSplitTorus.comp_iso` and `IsDerivedSubgroup.comp_iso`.
* `UnramifiedZeroDatum.zeroPoints_transport`:
  `(E.transport e).zeroPoints = E.zeroPoints.map e`. The `H(K)^♮` part is the published
  `map_simplyConnectedImage_eq`. The torus part is unchanged except that it is mapped by
  `i ≫ e`. The map of a join is the join of the maps.
* `map_mem_anisotropicZeroPoints`: assume `UnramifiedZeroPointsIndependenceStatement`, the
  independence part of KP Lemma 2.6.24. Then for every `F`-group `M`, every datum `E` for
  `M_K` and every automorphism `α : M ≅ M`, `α` maps
  `anisotropicZeroPoints E = M(K)^0 ∩ M(F)` into itself. Proof: independence gives
  `(E.transport α_K).zeroPoints = E.zeroPoints`, so `α_K` preserves `M(K)^0`. Then
  `rationalExtend_map` moves `α` past `M(F) → M(K)`.

## Provenance

This is internal infrastructure for KP Lemma 2.6.24 (printed p.104–105/PDF p.135–136). Its
proof uses that conjugation carries the subgroup defined by one choice to the subgroup defined
by the conjugated choice, which this module states for an arbitrary automorphism. The
independence itself is the separate statement `UnramifiedZeroPointsIndependenceStatement`. It
enters only as the explicit hypothesis of `map_mem_anisotropicZeroPoints` and is not proved
here.

Source: Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Definition 2.6.23 and
Lemma 2.6.24, printed pp.104–105/PDF pp.135–136 (`kaletha-prasad-2023-bruhat-tits-new-approach`).

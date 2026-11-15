# Greenberg point models over equal-characteristic discrete valuation rings

This module proves the Library statement
`Langlands.GroupScheme.IntegralModel.EqualCharacteristicGreenbergPointModelStatement`
at an arbitrary universe `u`. The statement is defined in
`GreenbergPointModelCases.lean` and explained in `GreenbergPointModelCases.md`.
The theorem is

```lean
theorem Langlands.GroupScheme.IntegralModel.equalCharacteristicGreenbergPointModel :
    EqualCharacteristicGreenbergPointModelStatement.{u}
```

Here `R` is a discrete valuation ring in `Type u` with algebraically closed
residue field `k`, and `ringChar R = ringChar k`. Fix a level `n > 0` and a
smooth affine group scheme `X` over `R`. The theorem gives
`HasGreenbergPointModel R n X`, which requires all of the following:

* a smooth affine `k`-group `G`;
* a group isomorphism from the rational points of the base change of `X` to
  `R/𝔪ⁿ` (`congruenceBaseMap R n`) onto the rational points of `G`;
* for every smooth affine source `Z` and homomorphism `h : Z ⟶ X`, a smooth
  affine `k`-group `GZ`, a point isomorphism, and a homomorphism `GZ ⟶ G`
  that make the square of points commute;
* geometric connectedness of `GZ` whenever `Z` is geometrically connected.

The proof uses no proof of `GreenbergPointModelStatement`, and it changes no
Library file.

## Source

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), the paragraph
before Theorem A.4.19 and its proof (printed pp. 628–629, PDF pp. 659–660). In
equal characteristic they define `Grₙ(X) = R_{(o/𝔪ⁿ)/f}(X ×_o o/𝔪ⁿ)` as a
Weil restriction along a coefficient field `f → o/𝔪ⁿ`. In characteristic
`p > 0` with perfect residue field this is the canonical structure
[Ser79, II §4 Prop. 8]. In characteristic zero it is a non-canonical choice
[Ser79, II §4 Prop. 6]. The corrections (Kaletha–Prasad 2024, PDF p. 49) add
perfectness of the residue field. Here the residue field is algebraically closed
and hence perfect. The Lean proof follows this definition. It proves the
required properties (affine, smooth, points, naturality, geometric
connectedness) with the Library's affine Weil restriction and its own helper
modules. It does not use the cited Conrad–Gabber–Prasad results.

## Helper modules

* `EqualCharacteristicGreenberg/CoefficientField.lean`
  (`CoefficientField.md`) provides three results:
  * `congruenceResidue R n : R/𝔪ⁿ → k` and nilpotence of its kernel
    (`isNilpotent_ker_congruenceResidue`);
  * `exists_coefficientField`: a ring section `σ : k → R/𝔪ⁿ` of the residue
    map, under the hypotheses on the characteristic;
  * `congruenceRing_finite`: `R/𝔪ⁿ` is a finite `k`-module through `σ`.
* `EqualCharacteristicGreenberg/WeilPoints.lean` (`WeilPoints.md`) provides:
  * `weilRationalPointsEquiv`: for a finite projective `A → B`, a group
    isomorphism between the rational points of `AffineWeil.groupScheme A B G`
    and those of `G`;
  * `weilRationalPointsEquiv_map`: its naturality in `AffineWeil.map`.
* `EqualCharacteristicGreenberg/Connected.lean` (`Connected.md`) provides
  `connectedSpace_weilRestriction`. If `O` is formally smooth and of finite type
  over `B`, has a `B`-point, and has a connected special fibre, then the
  finite-type Weil restriction of `O` along `k → B` has connected spectrum.

## This module

* `isPullback_specialFibre`: let `Y` be an affine scheme over `Spec B` with
  coordinate ring `O = AffineCoordinateRing B Y`. Then `Spec (k ⊗[B] O)` with
  the two maps shown is a pullback of `Y → Spec B ← Spec k`. Mathlib's
  `CommRingCat.isPushout_tensorProduct` and `isPullback_SpecMap_of_isPushout`
  give the pullback square for `Spec O`. It is pasted with the square of the
  isomorphism `affineSchemeOverIso B Y` between `Y` and `Spec O`.
* `isAffine_baseChange` and `smooth_baseChange`: let `Z` be affine over its
  base (`IsAffineHom`) and smooth. Then its base change along any
  `q : Spec B ⟶ Spec R` has affine total space and is smooth. These two
  results are local instances below.
* `geometricallyConnected_weilRestriction`: assume `k` is algebraically closed
  and `B` is a finite `k`-algebra with a retraction `B → k` that has nilpotent
  kernel. Let `Z` be smooth, affine and geometrically connected over `R`, and
  let `Z_B` be its base change along `q`. Then the Weil restriction
  `AffineWeil.groupScheme k B Z_B` is geometrically connected. The proof pastes
  `isPullback_specialFibre` with the base-change square. So `Spec (k ⊗[B] O)`
  is the fibre of `Z` over the point `Spec k → Spec B → Spec R`. The
  definition of `GeometricallyConnected` then makes it connected. The identity
  of `Z_B` gives a `B`-point of `O` (`affineSchemePointEquiv`,
  `ringTestSelfIso`). Smoothness of `Z_B` makes `O` formally smooth over `B`.
  So `connectedSpace_weilRestriction` makes the Weil restriction connected.
  The Library's `geometricallyConnected_of_connected_isAlgClosed` upgrades this
  to geometric connectedness over the algebraically closed field `k`.
* `exists_pointModel` has the conclusion of `HasGreenbergPointModel`, with
  `congruenceBaseMap R n` and `k` replaced by an arbitrary `q` and `k` as
  above. The models are `G = AffineWeil.groupScheme k B X_B` and
  `GZ = AffineWeil.groupScheme k B Z_B`, with `g = AffineWeil.map k B (h_B)`.
  Each comes with the following:
  * the inverse of `weilRationalPointsEquiv` as the point isomorphism;
  * `isAffineHom_of_isAffine` for affineness;
  * `AffineWeil.smooth_groupScheme` for smoothness.

  The square of points commutes by `weilRationalPointsEquiv_map`. Geometric
  connectedness is `geometricallyConnected_weilRestriction`.
* `equalCharacteristicGreenbergPointModel` (the target) chooses a coefficient
  field `σ` with `exists_coefficientField`. It sets the algebras
  `k → R/𝔪ⁿ := σ` and `R/𝔪ⁿ → k := congruenceResidue`. These form a scalar
  tower because `congruenceResidue ∘ σ = id`. Finiteness comes from
  `congruenceRing_finite`. The theorem then applies `exists_pointModel` with
  `B = R/𝔪ⁿ` and `q = congruenceBaseMap R n`. Nilpotence comes from
  `isNilpotent_ker_congruenceResidue`.

The proof depends only on the axioms `propext`, `Classical.choice` and
`Quot.sound`.

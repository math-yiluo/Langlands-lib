# Full V6 from root-coordinate equivariance

Author: Worker 1045.

This internal module reduces the centralizer compatibility V6 of a root
function family to data on each actual root group: a coordinate, or a finite
family of coordinates, with values in a finite extension `E / k`, and
characters through which the actual centralizer scales those coordinates. All statements hold at an arbitrary
universe `u`, in namespace `Langlands.Geometry.Building.IntegerValuation`.

## Setting

Let `k` be a field and `v : Valuation k (WithZero (Multiplicative ℤ))`, with
the real order `order v = -log v` used by `KPApartmentData`. Let `S` be a
commutative group scheme and `G`, `Z` group schemes over `Spec k`,
`i : S.toGrp ⟶ G` a monomorphism, `j : Z ⟶ G` representing the actual
centralizer `torusCentralizer i`, and `s : S.toGrp ⟶ Z` with
`h : Function.Bijective (Cartan.restrictionEvaluation s)`. The Library
predicate `IsCentralizerCompatible v i j s h φ` (module
`Langlands.Geometry.Building.IntegerCentralizer`) states, for every relative
root `a`, every `z ∈ Z(k)` and every `u` in the actual root group
`rootGroupPoints i a`,

```text
φ_a(j(z)⁻¹ u j(z)) = φ_a(u) + ⟨a, centralizerTranslation v s h z⟩,
```

where the translation is the negative of the integer centralizer valuation
`ν = centralizerValuation v s h`. This is KP Definition 6.1.2(V6) as formalized
in that module; `IsOmegaCompatible v D C` imposes it on every member of an
apartment class `D : KPApartmentData i (order v)` with an actual centralizer
datum `C`.

For a finite extension `E / k`, an additive valuation
`w : AddValuation E (WithTop ℝ)` is *norm-calibrated* for `v` if

```text
w(x) = order v (N_{E/k} x) / [E : k]      for every unit x of E.
```

## Declarations

- `IsNormCalibrated v w : Prop`, the definition above, with
  `Units.map (Algebra.norm k)` for the norm unit and `Module.finrank k E` for
  the degree.
- `IsNormCalibrated.apply_rationalCharacterEval hw α z`: for a norm-calibrated
  `w`, a rational character `α` of the base change `Z_E` and `z ∈ Z(k)`, the
  value `w(α(z_E))` is the published `characterNormOrder v α z`.
- `IsNormCalibrated.apply_inv hw x`: `w(x⁻¹) = -(order v (N x)) / [E : k]`.
- `isNormCalibrated_henselianIntegerAddValuation hH E`: if
  `hH : HenselianLocalRing v.valuationSubring` and `E / k` is finite Galois,
  the published `FieldTheory.henselianIntegerAddValuation v hH E` is
  norm-calibrated for `v`.
- `isNormCalibrated_henselianSeparableAddValuation hH E`: under the same
  `hH`, for a finite separable extension `E / k`, the published
  `FieldTheory.henselianSeparableAddValuation v hH E` is norm-calibrated for
  `v`.
- `nsmul_withTop_injective hm`: for `0 < m`, `x ↦ m • x` is injective on
  `WithTop ℝ`.
- The published `Langlands.Geometry.Building.eval_nsmul_char m a x`: `eval S (m • a) x = m * eval S a x` for the real pairing
  `RealTorusSpace.eval`.
- `conj_eq_of_coordinate v hj h φ a hw c hm hβ hval hconj z hu` (needs affine
  `Z`, `S`): the V6 equation for the single root `a`, at `z` and
  `u ∈ rootGroupPoints i a`, from the following hypotheses: `hw`, `w` is
  norm-calibrated; `c : G(k) → E` is a coordinate and `m` a positive natural
  number; `hβ`, the restriction of `β : rationalCharacters (Z_E)` along the
  base change of `s` is the base change of the `k`-character `m • a` of `S`;
  `hval`, `w(c(u)) = m • φ_a(u)` on the root group; `hconj`,
  `c(j(z)⁻¹ u j(z)) = β(z_E)⁻¹ · c(u)` on the root group for every `z`.
- `RootCoordinateEquivariance v i j s φ a`, a structure bundling these data:
  the field `E` with `Field`, `Algebra k E` and `FiniteDimensional k E` (all
  three declared as instances), `w`, `isNormCalibrated`, `coord`, `m`, `pos`,
  `character`, `restrict_eq`, `value` and `conj`, exactly as in
  `conj_eq_of_coordinate`.
- `RootCoordinateEquivariance.conj_eq hj h R z hu`: the V6 equation for the
  root `a` from `R : RootCoordinateEquivariance v i j s φ a`.
- `RootCoordinateEquivariance.ofMulEquiv hw e β hβ hφ hconj`: a constructor with
  `m = 1` from a group isomorphism `e : Multiplicative E ≃* rootGroupPoints i a`
  with `φ_a(e(x)) = w(x)` for all `x : E`, a character `β` whose restriction is
  the base change of `a`, and
  `j(z)⁻¹ e(x) j(z) = e(β(z_E)⁻¹ x)` for all `z ∈ Z(k)` and `x : E`. The
  coordinate is `e⁻¹` on the root group and `0` elsewhere.
- `conj_eq_of_coordinateFamily v hj h φ a hw c hm hβ hval hconj z hu` (needs
  affine `Z`, `S`): the same V6 equation from a finite family of coordinates.
  The index type `J : Type u` is finite and nonempty, `c : J → G(k) → E`, and
  `β : J → rationalCharacters (Z_E)`. The hypotheses are: `hβ`, every `β l`
  restricts along the base change of `s` to the base change of `m • a`;
  `hval`, `m • φ_a(u)` is the minimum over `l` of `w(c l u)` (written
  `Finset.univ.inf' Finset.univ_nonempty`) on the root group; `hconj`,
  `c l (j(z)⁻¹ u j(z)) = β l (z_E)⁻¹ · c l u` on the root group for every `l`
  and `z`.
- `RootCoordinateFamilyEquivariance v i j s φ a`, a structure bundling these
  data: the field `E` with its three instances, `w`, `isNormCalibrated`, the
  index type `J` with `Fintype` and `Nonempty` (all declared as instances),
  `coord`, `m`, `pos`, `character`, `restrict_eq`, `value` and `conj`, exactly
  as in `conj_eq_of_coordinateFamily`.
- `RootCoordinateFamilyEquivariance.conj_eq hj h R z hu`: the V6 equation for
  the root `a` from a coordinate family `R`.
- `RootCoordinateEquivariance.toFamily R`: single coordinate data as the
  one-member family indexed by `PUnit`, with the same field, valuation,
  multiplicity and character.
- `isCentralizerCompatible_of_rootCoordinateFamilies hj h hc`: if
  `Nonempty (RootCoordinateFamilyEquivariance v i j s φ a)` for every
  `a ∈ relativeRoots i`, then `IsCentralizerCompatible v i j s h φ`.
- `isCentralizerCompatible_of_rootCoordinates hj h hc`: if
  `Nonempty (RootCoordinateEquivariance v i j s φ a)` for every
  `a ∈ relativeRoots i`, then `IsCentralizerCompatible v i j s h φ`.
- `isOmegaCompatible_of_rootCoordinates hφ hc` (needs `IsAffineHom G.X.hom`
  and affine `S`): for `D : KPApartmentData i (order v)`, an actual
  `C : CentralizerDatum i` and `φ ∈ D.carrier`, coordinate data for `C.j`,
  `C.s` on every relative root give `IsOmegaCompatible v D C`.
- `isOmegaCompatible_of_rootCoordinateFamilies hφ hc`: the same with a
  coordinate family for `C.j`, `C.s` on every relative root.

## Proofs

1. `apply_rationalCharacterEval` is the calibration applied to the unit
   `α(z_E)`; its right side is the definition of `characterNormOrder`.
   `apply_inv` rewrites `N(x⁻¹) = N(x)⁻¹` and `order v` of an inverse.
2. For `isNormCalibrated_henselianIntegerAddValuation`, write
   `w(x) = r` with `r : ℝ` (a unit has finite value). The published
   `henselianIntegerAddValuation_norm` gives `w(N x) = [E : k] • r`, and
   `henselianIntegerAddValuation_base` identifies `w(N x)` with
   `-log v (N x)`, which is `order v (N x)` by `orderUnits_toAdd`. Dividing by
   the positive degree gives the claim.
   `isNormCalibrated_henselianSeparableAddValuation` is the same argument with
   the published `henselianSeparableAddValuation_norm` and
   `henselianSeparableAddValuation_base`.
3. `nsmul_withTop_injective` separates the value `⊤` (fixed by positive
   multiples) from real values, where it cancels the positive factor.
   The published `eval_nsmul_char` from `RootDatumValuation` supplies character additivity.
4. In `conj_eq_of_coordinate`, the conjugate `j(z)⁻¹ u j(z)` stays in the root
   group: centralizer points map to the normalizer with trivial Weyl action
   (`centralizerToNormalizer`, `weylAction_centralizerToNormalizer`), and
   `conj_mem_rootGroupPoints` applies. Multiply the goal by `m` (step 3). Then
   `hval`, `hconj`, multiplicativity of `w` and `apply_inv` turn the left side
   into `-characterNormOrder v β z + m • φ_a(u)`. The published
   `characterNormOrder_eq_eval` with `hβ` and `eval_nsmul_char` gives
   `characterNormOrder v β z = m * ⟨a, ν(z)⟩`, and
   `centralizerTranslation_toAdd` gives the translation `-ν(z)`.
5. `ofMulEquiv` checks the structure fields: the coordinate of `e(x)` is `x`,
   and every `u` in the root group is `e` of its coordinate. Hence
   `value` follows from `hφ` and `conj` from `hconj`.
6. In `conj_eq_of_coordinateFamily`, the conjugate stays in the root group as
   in step 4. The computation of step 4, applied to each member, gives
   `w(c l (j(z)⁻¹ u j(z))) = w(c l u) + C` for every `l`, with
   `C = m • ⟨a, centralizerTranslation v s h z⟩` in `WithTop ℝ`. After
   multiplying the goal by `m`, both sides are minima by `hval`, and the
   minimum of the shifted values is the shifted minimum: `x ↦ x + C` is
   monotone on `WithTop ℝ`, and Mathlib's `map_finset_inf'` applies to this
   order homomorphism.
7. `toFamily` reuses every field; its `value` holds because the minimum of a
   constant family over the nonempty index set is that constant
   (`Finset.inf'_const`).
8. `isCentralizerCompatible_of_rootCoordinates` and
   `isCentralizerCompatible_of_rootCoordinateFamilies` apply `conj_eq` to a
   chosen witness for each root. `isOmegaCompatible_of_rootCoordinates` and
   `isOmegaCompatible_of_rootCoordinateFamilies` derive affineness of `G` and
   of `C.Z` (from the closed immersion `C.isClosedSubgroup`), then apply the
   published `isOmegaCompatible_iff_of_mem`.

## Provenance and scope

This is a derived module assembled from Library declarations: the V6
predicates, centralizer valuation and translation of
`Langlands.Geometry.Building.IntegerCentralizer`, `characterNormOrder` and
`characterNormOrder_eq_eval` of `Langlands.Geometry.Building.CentralizerNormValuation`,
and the henselian valuations of `Langlands.FieldTheory.HenselianIntegerAddValuation` and
`Langlands.FieldTheory.HenselianSeparableIntegerAddValuation`.
It makes no independent literature assertion. The coordinate hypothesis
`j(z)⁻¹ e(x) j(z) = e(β(z_E)⁻¹ x)` is the usual form of the action of the
centralizer on a root group of a quasi-split group; it is assumed here, not
proved. The family form needs no identification of the root group with a
field or a vector space: any finite family of `E`-valued coordinates, each
scaled by the centralizer through a character restricting to `m • a`, whose
minimum computes `m • φ_a`, suffices. No such family is constructed here.

It is a partial contribution toward task 8ffe0456 (quasi-split apartments over
henselian integer-valued fields). It constructs no root-group coordinates,
proves no equivariance of actual coordinates, constructs no root function
family or apartment, and does not prove
`QuasiSplitIntegerApartmentExistenceStatement`. The henselian bridges cover
finite Galois and finite separable extensions; for other coordinate fields a
norm-calibrated valuation must be supplied.

# Normalized pullback on actual L² spaces

Authors: Worker 452 and Worker 378.

This module builds the normalized pullback operator between Mathlib's actual
complex almost-everywhere L² quotients `Lp ℂ 2 ν` and `Lp ℂ 2 μ`. All
declarations are in the namespace `Langlands.NormalizedL2Pullback`.

## Provenance

This is an internal construction. It does not transcribe a result from
external literature. It uses Mathlib's measure pushforward API
(`Measure.map`, `Measure.map_smul`, `Measure.map_map`,
`MeasurableEquiv.map_symm_map`), its Lp-seminorm API (`MemLp.comp_of_map`,
`MemLp.smul_measure`, `eLpNorm_comp_measurePreserving`,
`eLpNorm_smul_measure_of_ne_top'`) and its Lp quotient API (`MemLp.toLp`,
`MemLp.coeFn_toLp`, `Lp.ext`, `Lp.coeFn_add`, `Lp.coeFn_smul`,
`Lp.norm_def`), together with `NNReal.sqrt`. The module imports only Mathlib.

## Hypotheses

`X`, `Y` and `Z` are measurable spaces in independent universes `uX`, `uY`
and `uZ`, with measures `μ : Measure X`, `ν : Measure Y` and
`η : Measure Z`. The data are a measurable equivalence `e : X ≃ᵐ Y`, a
scalar `c : ℝ≥0` (finite and nonnegative) and an explicit proof
`hmap : μ.map e = c • ν`. There is no topology, local compactness,
sigma-finiteness or nonzero-measure assumption. The law `hmap` is always a
hypothesis; nothing in the module derives a measure law from topology, Haar
measure or a coordinate homeomorphism.

## Unnormalized pullback (any `c`, including `c = 0`)

- `quasiMeasurePreserving e c hmap : Measure.QuasiMeasurePreserving e μ ν`.
  The map `e` is measurable, and `μ.map e = c • ν` is absolutely continuous
  with respect to `ν` (`AbsolutelyContinuous.smul_left`). So almost-everywhere
  equalities for `ν` pull back along `e` to almost-everywhere equalities for
  `μ`.
- `memLp_comp e c hmap f : MemLp (f ∘ e) 2 μ` for `f : Lp ℂ 2 ν`. By
  `MemLp.comp_of_map` it suffices that `f` is in L² for `μ.map e = c • ν`.
  This holds by `MemLp.smul_measure`, because `c` is finite.
- `pullback e c hmap : Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 μ` is the Lp quotient map
  `f ↦ (memLp_comp e c hmap f).toLp (f ∘ e)` (`pullback_apply`, by `rfl`).
  Its representative is `f ∘ e` almost everywhere for `μ`
  (`coeFn_pullback`). The proofs of additivity and complex homogeneity use
  `Lp.ext`. They combine the `toLp` representatives, the Lp addition and
  scalar representative formulas, and the almost-everywhere formulas for
  `f + g` and `a • f`, transported along `e` by `quasiMeasurePreserving`.
- `norm_pullback`: `‖pullback e c hmap f‖ = (NNReal.sqrt c : ℝ) * ‖f‖`. By
  `Lp.norm_def`, the norm is the real part of `eLpNorm` at exponent 2. After
  replacing the representative by `f ∘ e`, `e` is measure-preserving from `μ`
  to `c • ν`. So `eLpNorm_comp_measurePreserving` turns the seminorm into
  `eLpNorm f 2 (c • ν)`. `eLpNorm_smul_measure_of_ne_top'` turns this into
  `c ^ (2 : ℝ≥0∞).toReal⁻¹ • eLpNorm f 2 ν`. `simp` then takes real parts
  (`ENNReal.toReal_mul`) and rewrites the power as `NNReal.sqrt c`
  (`NNReal.sqrt_eq_rpow`).

## Normalization scalar

`normalization c : ℂ` is defined for every `c : ℝ≥0` as
`((NNReal.sqrt c : ℝ) : ℂ)⁻¹`. When `c ≠ 0` it is the positive inverse square
root of `c`. Lean's convention `0⁻¹ = 0` makes `normalization 0 = 0`; the
normalized operators below are only formed for `c ≠ 0`. The proved scalar
identities are:

- `normalization_one : normalization 1 = 1` (a simp lemma);
- `norm_normalization : ‖normalization c‖ = (NNReal.sqrt c : ℝ)⁻¹`;
- `normalization_mul : normalization (c * d) = normalization c * normalization d`
  (from `NNReal.sqrt_mul`);
- `normalization_inv : normalization c⁻¹ = (normalization c)⁻¹`
  (from `NNReal.sqrt_inv`);
- `normalization_ne_zero : c ≠ 0 → normalization c ≠ 0`.

Only `normalization_ne_zero` has a hypothesis on the scalar; the other
identities hold for all `c, d : ℝ≥0`.

## Normalized isometry (`c ≠ 0`)

For `hc : c ≠ 0`, `normalized e c hc hmap : Lp ℂ 2 ν →ₗᵢ[ℂ] Lp ℂ 2 μ` is the
linear map `normalization c • pullback e c hmap`
(`normalized_apply`, by `rfl`). Its almost-everywhere representative is
`x ↦ normalization c • f (e x)` (`coeFn_normalized`), obtained from
`Lp.coeFn_smul` and `coeFn_pullback`. The isometry property follows from
`norm_smul`, `norm_normalization` and `norm_pullback`: the factor
`(NNReal.sqrt c)⁻¹ * NNReal.sqrt c` equals 1 because `NNReal.sqrt c ≠ 0`.

## Reciprocal law and inverse

- `map_symm e c hc hmap : ν.map e.symm = c⁻¹ • μ`. The proof maps `hmap` along
  `e.symm`. `MeasurableEquiv.map_symm_map` and `Measure.map_smul` give
  `c • ν.map e.symm = μ`; multiplying by `c⁻¹` uses `c ≠ 0`. This law fails in
  general for `c = 0`, so `hc` is needed.
- `normalized_symm_apply`: the normalized operator for `e.symm`, `c⁻¹` and
  `map_symm`, applied after `normalized e c hc hmap`, is the identity of
  `Lp ℂ 2 ν`. `normalized_apply_symm`: the composition in the other order is the
  identity of `Lp ℂ 2 μ`. Both proofs use `Lp.ext`. The outer representative
  formula is combined with the inner one, transported along the
  quasi-measure-preserving map (`e.symm` and `e` respectively). By
  `normalization_inv` and `normalization_ne_zero`, the product of
  `normalization c⁻¹` and `normalization c` (in either order) is 1. Then
  `e (e.symm y) = y` or `e.symm (e x) = x` finishes.
- `isometryEquiv e c hc hmap : Lp ℂ 2 ν ≃ₗᵢ[ℂ] Lp ℂ 2 μ` packages `normalized e
  c hc hmap` with the inverse `normalized e.symm c⁻¹ (inv_ne_zero hc)
  (map_symm e c hc hmap)`.

These formulas are exported:

- `isometryEquiv_apply`: `isometryEquiv e c hc hmap f = normalized e c hc hmap f`;
- `isometryEquiv_symm_apply`: `(isometryEquiv e c hc hmap).symm f` is
  `normalized e.symm c⁻¹ _ (map_symm e c hc hmap) f`;
- `isometryEquiv_symm`: `(isometryEquiv e c hc hmap).symm` equals
  `isometryEquiv e.symm c⁻¹ (inv_ne_zero hc) (map_symm e c hc hmap)`;
- `coeFn_isometryEquiv`: the representative of `isometryEquiv e c hc hmap f`
  is `x ↦ normalization c • f (e x)`, `μ`-almost everywhere;
- `coeFn_isometryEquiv_symm`: the representative of
  `(isometryEquiv e c hc hmap).symm f` is
  `y ↦ normalization c⁻¹ • f (e.symm y)`, `ν`-almost everywhere.

## Identity and composition

- `map_refl : μ.map (MeasurableEquiv.refl X) = (1 : ℝ≥0) • μ`. The identity
  equivalence acts as `id`, and `simp` closes the goal.
- `normalized_refl` (simp): `normalized (MeasurableEquiv.refl X) 1 one_ne_zero
  map_refl f = f`. The proof combines `coeFn_normalized` with
  `normalization_one`. `isometryEquiv_refl` (simp) states that the
  equivalence is `LinearIsometryEquiv.refl ℂ (Lp ℂ 2 μ)`.
- `map_trans`: for `d : Y ≃ᵐ Z`, `he : μ.map e = c • ν` and
  `hd : ν.map d = b • η`, we have `μ.map (e.trans d) = (c * b) • η`. The proof
  rewrites `e.trans d` as `d ∘ e` and applies `Measure.map_map`, `he`,
  `Measure.map_smul`, `hd` and `smul_smul`.
- `normalized_comp`: for `hc : c ≠ 0` and `hb : b ≠ 0`,

  ```text
  normalized e c hc he (normalized d b hb hd f)
    = normalized (e.trans d) (c * b) (mul_ne_zero hc hb) (map_trans e d c b he hd) f
  ```

  for `f : Lp ℂ 2 η`. The proof uses `Lp.ext`. The representative formula of
  the inner operator is transported along `e`, and the outer and composite
  representative formulas are substituted. `smul_smul` gives the scalar
  `normalization c * normalization b`, which is `normalization (c * b)` by
  `normalization_mul`. The remaining equality holds by `rfl`, since
  `(e.trans d) x` is definitionally `d (e x)`.
- `isometryEquiv_trans`: the same law for equivalences.

  ```text
  (isometryEquiv d b hb hd).trans (isometryEquiv e c hc he)
    = isometryEquiv (e.trans d) (c * b) (mul_ne_zero hc hb) (map_trans e d c b he hd)
  ```

  Here `LinearIsometryEquiv.trans` applies the pullback along `d`
  (`Lp ℂ 2 η → Lp ℂ 2 ν`) first and the pullback along `e`
  (`Lp ℂ 2 ν → Lp ℂ 2 μ`) second. So pullback reverses the order of
  composition of `e.trans d`, which applies `e` first.

## Scope

The module proves no Haar-measure or determinant scaling law and no
quotient-measure transport. It has no affine specialization, no group action
or strong continuity, no Fourier operators, no general semidirect Hilbert
induction, no smooth-vector comparison and no irreducibility statement.

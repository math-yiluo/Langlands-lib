# Averaging linear maps between `O(r)`-finite functions over `O(r)`

Module: `Langlands.Representation.Archimedean.RealInductionStagesAverage`.

## Purpose and provenance

This module is internal infrastructure for the proof of
`Langlands.Archimedean.RealAdjacentFiltrationInStagesStatement` (induction in stages of adjacent
filtrations). That proof needs linear maps between real standard modules on
`GL_r(ℝ)` that commute exactly with right translation by `O(r)`. Linear algebra alone only
gives maps that commute with `O(r)` modulo a subspace. This module averages such a map over
`O(r)` against the normalized Haar measure. The average commutes exactly with `O(r)` and still
agrees with the original map modulo the subspace. Commutation with right derivatives modulo an
`O(r)`-stable subspace also survives averaging.

Averaging over a compact group is a standard technique. This module makes no literature
assertion, so it has no literature sources. Integrals are pointwise: `(avg A f)(g)` is the
integral over `O(r)` of the values at `g`. The module
`Langlands.Representation.Archimedean.RealInductionStagesFamily` shows that such integrals stay
in the right finite-dimensional space and commute with linear maps.

All declarations are in the namespace `Langlands.Archimedean.InductionStages`. Throughout,
`r : ℕ`, `ds`, `es`, `fs : List RealBlock` are lists of real blocks, and
`haarK r = RealPrincipalSeriesDuality.haarK r` is the normalized Haar probability measure on
`O(r) = unitaryCompact ℝ r`. Its measurable structure is the Borel σ-algebra
(`RealPrincipalSeriesDuality.measurableSpaceK`, made a local instance). The module also adds a
local `BorelSpace` instance.

## Declarations

### `O(r)`-finite functions, right translation and right derivatives

- `KFin r ds` (abbreviation): the `O(r)`-finite functions
  `kFiniteFunctions (realStandardModule r ds) (unitaryCompact ℝ r)` of the real standard module
  of `ds`, a submodule of `GL_r(ℝ) → ℂ`.
- `toUnitary r : unitaryCompact ℝ r →* Matrix.unitaryGroup (Fin r) ℝ`: the subgroup `O(r)` of
  `GL_r(ℝ)` viewed as the group of orthogonal matrices (same underlying matrix,
  `coe_toUnitary`). `toUnits_toUnitary` recovers the element of `GL_r(ℝ)`.
- `kRep r ds k`: right translation `(R(k) f)(g) = f(g k)` by `k ∈ O(r)` on `KFin r ds`. It is
  the Library's `realStandardRep r ds` composed with `toUnitary r`. Lemmas: `kRep_apply_coe`
  (the formula), `kRep_mul` (`R(k k') = R(k) R(k')`), `kRep_one`, `kRep_inv_kRep`,
  `kRep_kRep_inv`.
- `lie r ds X`: the right derivative `R(X) = realStandardLie r ds (1 ⊗ X)` for a real
  `r × r` matrix `X`. By `lie_apply_coe` its value is the Library's
  `rightDerivative (matrixModel ℝ r) X f`.
- `adK r k X = k X kᵀ` (written `k * X * star k`): the adjoint action of `k ∈ O(r)`.
- `kRep_lie`: `R(k) R(X) f = R(k X k⁻¹) R(k) f`. This is the compatibility condition of the
  Library's `(𝔤, K)`-module structure, `isRealGKModule_realStandardModule`.
- `coe_inv_unitaryCompact`: the matrix of `k⁻¹` is `kᵀ`. `adK_inv_adK`:
  `adK (k⁻¹) (adK k X) = X`.
- `lie_kRep_inv`: `R(X) R(k⁻¹) f = R(k⁻¹) R(k X k⁻¹) f`, from `kRep_lie` and `adK_inv_adK`.

### Finite-dimensional `O(r)`-stable subspaces

- `exists_stable U`: every finite-dimensional subspace `U` of `KFin r ds` lies in a
  finite-dimensional subspace `S` that is stable under every `R(k)`. Proof: take a basis
  `b₁, …, b_d` of `U` and let `S` be the supremum of the `O(r)`-orbit spans of the `bᵢ`. Each
  orbit span is finite-dimensional because the module is a `(𝔤, K)`-module (first condition of
  `isRealGKModule_realStandardModule`) and is `O(r)`-stable (`orbitSubrepresentation`). The
  supremum is then `O(r)`-stable, by induction over the supremum (`Submodule.iSup_induction`).
- `kRep_mem_orbitSpan`: `R(k) f` lies in the orbit span of `f`.
- `finiteDimensional_orbitSpan` (instance): orbit spans are finite-dimensional.

### The conjugates `R(k)⁻¹ A R(k)`

Let `A : KFin r ds →ₗ[ℂ] KFin r es` be linear and `f ∈ KFin r ds`.

- `conj A k = R(k⁻¹) ∘ A ∘ R(k)` (`conj_apply`). By `conj_apply_coe`,
  `(conj A k f)(g) = (A (R(k) f))(g k⁻¹)`.
- `exists_conj_stable A f`: there is a finite-dimensional `O(r)`-stable `S` containing `A f`
  and every `conj A k f`. Proof: apply `exists_stable` to the image under `A` of the orbit span
  of `f`. It contains `A (R(k) f)`, and `S` is stable under `R(k⁻¹)`.
- `continuous_kRep_apply`: `k ↦ (R(k) f)(g)` is continuous, since `O(r)`-finite functions are
  continuous (`RealPrincipalSeriesDuality.continuous_of_mem_kFiniteFunctions`).
- `continuous_conj_apply A f g`: `k ↦ (conj A k f)(g)` is continuous. Proof: the functions
  `A (R(k) f)` lie in the finite-dimensional space `A(orbit span of f)` of continuous
  functions. They depend continuously on `k` pointwise (`continuous_map_of_mem`), so
  `(k, x) ↦ (A (R(k) f))(x)` is jointly continuous (`continuous_uncurry_of_mem`). Compose it
  with the continuous map `k ↦ (k, g k⁻¹)`. Continuity of `k ↦ k⁻¹` in `GL_r(ℝ)` is shown by
  `Units.continuous_iff`: the matrix of `k⁻¹` is `kᵀ`, and the matrix of its inverse is `k`.
- `integrable_conj_apply A f g`: `k ↦ (conj A k f)(g)` is `haarK r`-integrable, being
  continuous on a compact group (`RealPrincipalSeriesDuality.integrable_of_continuous`).
- `conj_kRep`: `conj A k (R(k₀) f) = R(k₀) (conj A (k k₀) f)`, by `kRep_mul` and
  `k₀ (k k₀)⁻¹ = k⁻¹`.

### The average

- `avg_mem A f`: the function `g ↦ ∫ (conj A k f)(g) d(haarK r)(k)` is `O(r)`-finite. Proof:
  `integral_mem` (from `RealInductionStagesFamily`) for the finite-dimensional space `S` of
  `exists_conj_stable`, viewed inside `GL_r(ℝ) → ℂ`.
- `avg A : KFin r ds →ₗ[ℂ] KFin r es`: the average, sending `f` to the function of `avg_mem`.
  Linearity follows from `integral_add` and `integral_const_mul`. `avg_apply_coe` states
  `(avg A f)(g) = ∫ (conj A k f)(g) dk`.
- `avg_kRep`: `avg A (R(k₀) f) = R(k₀) (avg A f)` exactly. Proof: by `conj_kRep`, the value at
  `g` of the left side is `∫ (conj A (k k₀) f)(g k₀) dk`. Right invariance of the Haar measure
  (`integral_mul_right_eq_self`, instance `isMulRightInvariant_haarK`) turns this into
  `∫ (conj A k f)(g k₀) dk = (avg A f)(g k₀)`.
- `avg_sub_mem A M f c h`: let `M` be a submodule of `KFin r es` and `c ∈ KFin r es`. If
  `conj A k f - c ∈ M` for every `k`, then `avg A f - c ∈ M`. Proof: `mem_of_integral` for the
  family `k ↦ conj A k f - c`. This family lies in the finite-dimensional space
  `S ⊔ span{c}`, and its pointwise integral is `avg A f - c` because `haarK r` is a
  probability measure (`integral_const`).
- `avg_mem_of_forall`: if `conj A k f ∈ M` for every `k`, then `avg A f ∈ M` (`c = 0`).
- `avg_sub_self_mem A M hM hA f`: if `M` is stable under every `R(k)` and
  `A (R(k) f') - R(k) (A f') ∈ M` for all `k` and `f'`, then `avg A f - A f ∈ M`. Proof:
  `conj A k f - A f = R(k⁻¹)(A (R(k) f) - R(k) (A f)) ∈ M`, then `avg_sub_mem` with `c = A f`.
- `avg_eq_self`: an exactly `O(r)`-equivariant `A` equals its average (`avg_sub_self_mem` with
  `M = ⊥`).
- `map_avg A B hB f`: if `B : KFin r es →ₗ[ℂ] KFin r fs` commutes exactly with every `R(k)`,
  then `B (avg A f) = avg (B ∘ A) f`. Proof: `map_integral_of_mem` gives
  `(B (avg A f))(g) = ∫ (B (conj A k f))(g) dk`, and `B (conj A k f) = conj (B ∘ A) k f` since
  `B` commutes with `R(k⁻¹)`.
- `lie_avg_sub_mem A M hM hA X f`: let `M` be stable under every `R(k)`, and suppose
  `R(Y) (A f') - A (R(Y) f') ∈ M` for every matrix `Y` and every `f'`. Then
  `R(X) (avg A f) - avg A (R(X) f) ∈ M`. Proof: by `map_integral_of_mem` for `L = R(X)`, the
  left side is the pointwise integral of `k ↦ R(X) (conj A k f) - conj A k (R(X) f)`. The
  first term is integrable: it is continuous by `continuous_map_of_mem`. The family lies in
  the finite-dimensional space `R(X)(S) ⊔ S'`, where `S'` is the space of `exists_conj_stable`
  for `R(X) f`. By `lie_kRep_inv` and `kRep_lie`, each member equals
  `R(k⁻¹)(R(Y) (A (R(k) f)) - A (R(Y) (R(k) f)))` with `Y = k X k⁻¹`, so it lies in `M`.
  Conclude by `mem_of_integral`.

import Langlands.Algebra.DivisionReducedNormValuation
import Langlands.Galois.Local.AbsoluteDefinitions

/-! Valuations on central division algebras over actual nonarchimedean local fields. -/

noncomputable section

namespace Langlands.CentralDivision

open scoped TensorProduct WithZero
open Langlands.CentralSimple ValuativeRel

universe u

variable (K D : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]

/-- The given local-field valuation of the canonical reduced norm is ultrametric. -/
theorem valuation_reducedNorm_add_le (x y : D) :
    valuation K (reducedNorm K D K (1 ⊗ₜ[K] (x + y))) ≤
      max (valuation K (reducedNorm K D K (1 ⊗ₜ[K] x)))
        (valuation K (reducedNorm K D K (1 ⊗ₜ[K] y))) := by
  let := LocalGalois.localNormedField K
  let := LocalGalois.localNormedField_complete K
  let := LocalGalois.localNormedField_ultrametric K
  have h := norm_reducedNorm_add_le K D x y
  rw [le_max_iff] at h ⊢
  exact h.imp (LocalGalois.localNormedField_le K _ _).mp
    (LocalGalois.localNormedField_le K _ _).mp

/-- The canonical reduced-norm valuation with values in the original base value group. -/
def localReducedNormValuation : Valuation D (ValueGroupWithZero K) where
  toFun x := valuation K (reducedNorm K D K (1 ⊗ₜ[K] x))
  map_zero' := by simp
  map_one' := by
    simp only [← Algebra.TensorProduct.includeRight_apply, map_one]
  map_mul' x y := by
    simp only [← Algebra.TensorProduct.includeRight_apply, map_mul]
  map_add_le_max' := valuation_reducedNorm_add_le K D

@[simp]
theorem localReducedNormValuation_apply (x : D) :
    localReducedNormValuation K D x =
      valuation K (reducedNorm K D K (1 ⊗ₜ[K] x)) := rfl

@[simp]
theorem localReducedNormValuation_algebraMap (a : K) :
    localReducedNormValuation K D (algebraMap K D a) =
      valuation K a ^ reducedDegree K D := by
  change valuation K (reducedNorm K D K (1 ⊗ₜ[K] algebraMap K D a)) = _
  rw [← Algebra.TensorProduct.algebraMap_apply', Algebra.TensorProduct.algebraMap_apply]
  simp only [Algebra.algebraMap_self_apply, reducedNorm_scalar, map_pow]

/-- The regular determinant norm gives the reduced-degree power of the local valuation. -/
theorem valuation_regularNorm_eq_localReducedNormValuation_pow (x : D) :
    valuation K (Algebra.norm K x) =
      localReducedNormValuation K D x ^ reducedDegree K D := by
  rw [regularNorm_eq_reducedNorm_pow, map_pow]
  rfl

instance localReducedNormValuation_isNontrivial :
    (localReducedNormValuation K D).IsNontrivial := by
  obtain ⟨a, ha, hlt⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation K)
  apply (localReducedNormValuation K D).isNontrivial_iff_exists_lt_one.mpr
  refine ⟨algebraMap K D a, (map_ne_zero _).mpr ha, ?_⟩
  rw [localReducedNormValuation_algebraMap]
  exact pow_lt_one₀ zero_le hlt (reducedDegree_pos K D).ne'

/-- The same valuation transported through the intrinsic discrete base value-group isomorphism. -/
def localReducedNormIntValuation : Valuation D ℤᵐ⁰ :=
  (localReducedNormValuation K D).map
    (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).toMonoidWithZeroHom
    (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).toOrderIso.monotone

@[simp]
theorem localReducedNormIntValuation_apply (x : D) :
    localReducedNormIntValuation K D x =
      IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
        (valuation K (reducedNorm K D K (1 ⊗ₜ[K] x))) := rfl

@[simp]
theorem localReducedNormIntValuation_algebraMap (a : K) :
    localReducedNormIntValuation K D (algebraMap K D a) =
      (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K (valuation K a)) ^
        reducedDegree K D := by
  change IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
      (localReducedNormValuation K D (algebraMap K D a)) = _
  rw [localReducedNormValuation_algebraMap, map_pow]

/-- Transport to the discrete value group preserves the valuation comparisons. -/
theorem localReducedNormIntValuation_le_iff (x y : D) :
    localReducedNormIntValuation K D x ≤ localReducedNormIntValuation K D y ↔
      localReducedNormValuation K D x ≤ localReducedNormValuation K D y :=
  (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).toOrderIso.le_iff_le

end Langlands.CentralDivision

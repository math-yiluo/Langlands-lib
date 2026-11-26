import Langlands.Global.RankinSelberg.RealExactCompactProjection
import Langlands.Global.RankinSelberg.RealAdjacentCanonicalChamber
import Langlands.Representation.Archimedean.SmoothKFiniteAdmissibility

/-! # Compact projection along the orthogonal matrix group

See the paired Markdown file.
-/

noncomputable section

open MeasureTheory

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealJacquet

open Langlands.Archimedean

local instance realOrthogonalCompactProjectionMeasurable (j : ℕ) :
    MeasurableSpace (unitaryCompact ℝ j) := borel _
local instance realOrthogonalCompactProjectionBorel (j : ℕ) :
    BorelSpace (unitaryCompact ℝ j) := ⟨rfl⟩

variable (n : ℕ)

/-- The orthogonal matrix group and the unitary compact subgroup of `GL_n(ℝ)` are isomorphic
topological groups: a unitary matrix is sent to itself, viewed as an invertible matrix. -/
def orthogonalUnitaryCompactEquiv :
    Matrix.unitaryGroup (Fin n) ℝ ≃ₜ* unitaryCompact ℝ n where
  toFun k := ⟨Unitary.toUnits k, k.prop⟩
  invFun k := unitaryCompactMatrix ℝ n k
  left_inv _ := rfl
  right_inv _ := Subtype.ext (Units.ext rfl)
  map_mul' _ _ := Subtype.ext (map_mul Unitary.toUnits _ _)
  continuous_toFun := (continuous_unitary_toUnits (F := ℝ) (N := n)).subtype_mk _
  continuous_invFun := continuous_unitaryCompactMatrix ℝ n

@[simp]
theorem orthogonalUnitaryCompactEquiv_apply_val (k : Matrix.unitaryGroup (Fin n) ℝ) :
    (orthogonalUnitaryCompactEquiv n k).val = Unitary.toUnits k :=
  rfl

variable {n}

/-- Compact projection along the orthogonal matrix group holds at every rank. -/
theorem realOrthogonalCompactProjectionPremise (r : ℕ) :
    RealOrthogonalCompactProjectionPremise r := by
  classical
  intro es a κ hκ hκfin B hB f g
  let O := Matrix.unitaryGroup (Fin (r + 1)) ℝ
  let Kc := unitaryCompact ℝ (r + 1)
  let e : O ≃ₜ* Kc := orthogonalUnitaryCompactEquiv (r + 1)
  let μ : Measure O := Measure.haar
  let ν : Measure Kc := μ.map e
  have hν : ν.IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map μ e
  let κ' : C(Kc, ℂ) := ⟨fun k => κ (e.symm k), hκ.comp e.symm.continuous⟩
  have hκ'fin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range
      fun h : Kc => fun k => κ' (h⁻¹ * k))) := by
    let T : (O → ℂ) →ₗ[ℂ] (Kc → ℂ) := LinearMap.funLeft ℂ ℂ e.symm
    have hle : Submodule.span ℂ (Set.range fun h : Kc => fun k => κ' (h⁻¹ * k)) ≤
        (Submodule.span ℂ (Set.range fun x : O => fun k => κ (x⁻¹ * k))).map T := by
      rw [Submodule.span_le]
      rintro _ ⟨h, rfl⟩
      refine Submodule.mem_map.mpr ⟨_, Submodule.subset_span ⟨e.symm h, rfl⟩, ?_⟩
      funext k
      simp only [T, LinearMap.funLeft_apply, κ', ContinuousMap.coe_mk, map_mul, map_inv]
    exact Submodule.finiteDimensional_of_le hle
  obtain ⟨p, hp, hBp⟩ := realExactCompactProjection r es a ν hν κ' hκ'fin B hB.1 f g
  have hint (F : Kc → ℂ) : ∫ k, F k ∂ν = ∫ k, F (e k) ∂μ :=
    e.toHomeomorph.measurableEmbedding.integral_map F
  refine ⟨p, fun x => ?_, fun x => ?_⟩
  · rw [hp, hint]
    refine integral_congr_ae (ae_of_all _ fun k => ?_)
    simp only [κ', ContinuousMap.coe_mk, ContinuousMulEquiv.symm_apply_apply]
    rfl
  · rw [hBp, hint]
    refine integral_congr_ae (ae_of_all _ fun k => ?_)
    simp only [κ', ContinuousMap.coe_mk, ContinuousMulEquiv.symm_apply_apply]
    rfl

end Langlands.Global.RankinSelbergGlobal.RealJacquet

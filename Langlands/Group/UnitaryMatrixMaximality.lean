import Langlands.Group.UnitaryMatrixMaximalityStatement
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact

universe u

namespace Langlands.Group

open Matrix

private theorem matrix_mem_unitary_of_norm {𝕜 : Type u} [RCLike 𝕜] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) 𝕜)
    (h : ∀ x : EuclideanSpace 𝕜 (Fin n), ‖Matrix.toEuclideanLin A x‖ = ‖x‖) :
    A ∈ Matrix.unitaryGroup (Fin n) 𝕜 := by
  let L : EuclideanSpace 𝕜 (Fin n) →ₗᵢ[𝕜] EuclideanSpace 𝕜 (Fin n) :=
    { toLinearMap := Matrix.toEuclideanLin A, norm_map' := h }
  let e := L.toLinearIsometryEquiv rfl
  have he := e.toMatrix_mem_unitaryGroup
    (EuclideanSpace.basisFun (Fin n) 𝕜) (EuclideanSpace.basisFun (Fin n) 𝕜)
  change LinearMap.toMatrix _ _ (Matrix.toEuclideanLin A) ∈ _ at he
  simpa only [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.toMatrix_toLin] using he

private theorem exists_unitary_map {𝕜 : Type u} [RCLike 𝕜] {n : ℕ}
    (x y : EuclideanSpace 𝕜 (Fin n)) (hx : x ≠ 0) (hxy : ‖x‖ = ‖y‖) :
    ∃ q : Matrix.unitaryGroup (Fin n) 𝕜,
      Matrix.toEuclideanLin (q : Matrix (Fin n) (Fin n) 𝕜) x = y := by
  let c := LinearEquiv.coord 𝕜 (EuclideanSpace 𝕜 (Fin n)) x hx
  let L : (𝕜 ∙ x) →ₗᵢ[𝕜] EuclideanSpace 𝕜 (Fin n) :=
    { toLinearMap := (LinearMap.toSpanSingleton 𝕜 _ y).comp c.toLinearMap
      norm_map' := by
        intro z
        change ‖c z • y‖ = ‖z‖
        rw [norm_smul, ← hxy, ← norm_smul]
        exact congrArg norm (LinearEquiv.coord_apply_smul 𝕜 _ x hx z) }
  let A : Matrix (Fin n) (Fin n) 𝕜 := Matrix.toEuclideanLin.symm L.extend.toLinearMap
  have hA : Matrix.toEuclideanLin A = L.extend.toLinearMap :=
    Matrix.toEuclideanLin.apply_symm_apply _
  refine ⟨⟨A, matrix_mem_unitary_of_norm A (by intro z; rw [hA]; exact L.extend.norm_map z)⟩, ?_⟩
  change Matrix.toEuclideanLin A x = y
  rw [hA]
  have he := L.extend_apply (⟨x, Submodule.mem_span_singleton_self x⟩ : 𝕜 ∙ x)
  change L.extend x = _ at he
  change L.extend x = y
  rw [he]
  change c ⟨x, Submodule.mem_span_singleton_self x⟩ • y = y
  rw [LinearEquiv.coord_self, one_smul]

private theorem continuous_matrix_action_norm {𝕜 : Type u} [RCLike 𝕜] {n : ℕ}
    (x : EuclideanSpace 𝕜 (Fin n)) :
    Continuous (fun g : Matrix.GeneralLinearGroup (Fin n) 𝕜 =>
      ‖Matrix.toEuclideanLin (g : Matrix (Fin n) (Fin n) 𝕜) x‖) := by
  apply Continuous.norm
  change Continuous (fun g : Matrix.GeneralLinearGroup (Fin n) 𝕜 =>
    WithLp.toLp 2 ((g : Matrix (Fin n) (Fin n) 𝕜) *ᵥ WithLp.ofLp x))
  apply (PiLp.continuous_toLp 2 (fun _ : Fin n => 𝕜)).comp
  have hv : Continuous (fun g : Matrix.GeneralLinearGroup (Fin n) 𝕜 =>
      (g : Matrix (Fin n) (Fin n) 𝕜)) := Units.continuous_val
  exact hv.matrix_mulVec continuous_const

private theorem compact_overgroup_norm_le {𝕜 : Type u} [RCLike 𝕜] {n : ℕ}
    (U : Subgroup (Matrix.GeneralLinearGroup (Fin n) 𝕜))
    (hU : IsCompact (U : Set (Matrix.GeneralLinearGroup (Fin n) 𝕜)))
    (hcontains : ∀ q : Matrix.unitaryGroup (Fin n) 𝕜, Unitary.toUnits q ∈ U)
    (g : Matrix.GeneralLinearGroup (Fin n) 𝕜) (hg : g ∈ U)
    (x : EuclideanSpace 𝕜 (Fin n)) :
    ‖Matrix.toEuclideanLin (g : Matrix (Fin n) (Fin n) 𝕜) x‖ ≤ ‖x‖ := by
  classical
  by_cases hx : x = 0
  · simp [hx]
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  obtain ⟨a, ha, hmax⟩ := hU.exists_isMaxOn ⟨1, U.one_mem⟩
    (continuous_matrix_action_norm x).continuousOn
  let y := Matrix.toEuclideanLin (a : Matrix (Fin n) (Fin n) 𝕜) x
  have hxr : ‖x‖ ≤ ‖y‖ := by
    simpa [y, Matrix.toEuclideanLin] using hmax U.one_mem
  have hypos : 0 < ‖y‖ := hxpos.trans_le hxr
  let c : 𝕜 := ((‖y‖ / ‖x‖ : ℝ) : 𝕜)
  have hc : ‖c‖ = ‖y‖ / ‖x‖ := by
    simp only [c, RCLike.norm_ofReal, abs_of_nonneg (div_nonneg (norm_nonneg _) (norm_nonneg _))]
  have hxy : ‖y‖ = ‖c • x‖ := by
    rw [norm_smul, hc, div_mul_cancel₀ _ hxpos.ne']
  obtain ⟨q, hq⟩ := exists_unitary_map y (c • x) (norm_ne_zero_iff.mp hypos.ne') hxy
  have hprod := hmax (U.mul_mem (U.mul_mem ha (hcontains q)) ha)
  have heq : Matrix.toEuclideanLin
      ((a * Unitary.toUnits q * a : Matrix.GeneralLinearGroup (Fin n) 𝕜) :
        Matrix (Fin n) (Fin n) 𝕜) x = c • y := by
    simp only [Units.val_mul, Matrix.toEuclideanLin, Matrix.toLpLin_mul_same,
      LinearMap.comp_apply]
    change Matrix.toEuclideanLin (a : Matrix (Fin n) (Fin n) 𝕜)
      (Matrix.toEuclideanLin (q : Matrix (Fin n) (Fin n) 𝕜) y) = c • y
    rw [hq, map_smul]
  change ‖Matrix.toEuclideanLin _ x‖ ≤ ‖y‖ at hprod
  rw [heq, norm_smul, hc] at hprod
  have hratio : ‖y‖ / ‖x‖ ≤ 1 := by
    nlinarith
  have hyr : ‖y‖ ≤ ‖x‖ := (div_le_one hxpos).mp hratio
  exact (hmax hg).trans hyr

/-- Every compact matrix subgroup containing the unitary group consists of unitary matrices. -/
theorem unitaryMatrixCompactOvergroup (𝕜 : Type u) [RCLike 𝕜] (n : ℕ) :
    UnitaryMatrixCompactOvergroupStatement 𝕜 n := by
  intro U hU hcontains g hg
  apply matrix_mem_unitary_of_norm
  intro x
  apply le_antisymm (compact_overgroup_norm_le U hU hcontains g hg x)
  have h := compact_overgroup_norm_le U hU hcontains g⁻¹ (U.inv_mem hg)
    (Matrix.toEuclideanLin (g : Matrix (Fin n) (Fin n) 𝕜) x)
  have hinv : Matrix.toEuclideanLin (↑g⁻¹ : Matrix (Fin n) (Fin n) 𝕜)
      (Matrix.toEuclideanLin (g : Matrix (Fin n) (Fin n) 𝕜) x) = x := by
    rw [Matrix.toEuclideanLin,
      ← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same, Units.inv_mul, Matrix.toLpLin_one]
    rfl
  rwa [hinv] at h

example : ∀ (𝕜 : Type u) [RCLike 𝕜] (n : ℕ),
    UnitaryMatrixCompactOvergroupStatement 𝕜 n := @unitaryMatrixCompactOvergroup

end Langlands.Group

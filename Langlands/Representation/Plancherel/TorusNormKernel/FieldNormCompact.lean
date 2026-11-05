import Mathlib.RingTheory.Norm.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Seminorm.Norm
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Compactness of bounded-norm sets in a finite field extension

Let `F` be a nontrivially normed field whose closed balls are compact, and let `E` be a
finite field extension of `F` with its canonical module topology. The set of elements whose
field norm to `F` is bounded is compact, and so is the set of units of norm one.
-/

noncomputable section

open Topology

namespace Langlands.Plancherel.TorusNormKernel

variable {F : Type*} [NontriviallyNormedField F]
variable {E : Type*} [Field E] [Algebra F E] [FiniteDimensional F E]
variable [TopologicalSpace E] [IsModuleTopology F E]

/-- The coordinate equivalence of a finite basis is a homeomorphism for the module topology. -/
def coordinateHomeomorph : E ≃ₜ (Fin (Module.finrank F E) → F) :=
  haveI : ContinuousAdd E := IsModuleTopology.toContinuousAdd F E
  let e := (Module.finBasis F E).equivFun
  { toEquiv := e.toEquiv
    continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }

theorem coordinateHomeomorph_apply (x : E) :
    coordinateHomeomorph (F := F) (E := E) x = (Module.finBasis F E).equivFun x :=
  rfl

theorem coordinateHomeomorph_symm_apply (v : Fin (Module.finrank F E) → F) :
    (coordinateHomeomorph (F := F) (E := E)).symm v = (Module.finBasis F E).equivFun.symm v :=
  rfl

include F in
theorem t2Space_of_moduleTopology : T2Space E :=
  (coordinateHomeomorph (F := F) (E := E)).isEmbedding.t2Space

/-- The field norm is continuous for the module topology. -/
theorem continuous_algebraNorm : Continuous (Algebra.norm F : E → F) := by
  classical
  let b := Module.finBasis F E
  have h : (Algebra.norm F : E → F) = fun x => (Algebra.leftMulMatrix b x).det :=
    funext fun x => Algebra.norm_eq_matrix_det b x
  rw [h]
  refine Continuous.matrix_det ?_
  refine continuous_pi fun i => continuous_pi fun j => ?_
  have hij : (fun x : E => Algebra.leftMulMatrix b x i j) =
      fun x => (b.coord i).comp (LinearMap.mulRight F (b j)) x := by
    funext x
    rw [Algebra.leftMulMatrix_eq_repr_mul]
    rfl
  rw [hij]
  exact IsModuleTopology.continuous_of_linearMap _

variable [ProperSpace F]

/-- Elements of a finite field extension whose norm is bounded form a compact set. -/
theorem isCompact_algebraNorm_le (M : ℝ) : IsCompact {x : E | ‖Algebra.norm F x‖ ≤ M} := by
  classical
  set d := Module.finrank F E
  set e := coordinateHomeomorph (F := F) (E := E)
  let ν : (Fin d → F) → F := fun v => Algebra.norm F (e.symm v)
  have hν : Continuous ν := (continuous_algebraNorm (F := F) (E := E)).comp e.symm.continuous
  have hνsmul : ∀ (c : F) (v : Fin d → F), ν (c • v) = c ^ d * ν v := by
    intro c v
    have h : e.symm (c • v) = c • e.symm v := by
      rw [coordinateHomeomorph_symm_apply, coordinateHomeomorph_symm_apply, map_smul]
    change Algebra.norm F (e.symm (c • v)) = c ^ d * Algebra.norm F (e.symm v)
    rw [h, Algebra.smul_def, map_mul, Algebra.norm_algebraMap]
  have hνzero : ∀ v, ν v = 0 → v = 0 := by
    intro v hv
    have h0 : e.symm v = 0 := Algebra.norm_eq_zero_iff.mp hv
    have h1 := e.apply_symm_apply v
    rw [h0, coordinateHomeomorph_apply, map_zero] at h1
    exact h1.symm
  have hdpos : 0 < d := Module.finrank_pos
  set SV := {v : Fin d → F | ‖ν v‖ ≤ M}
  have hSVclosed : IsClosed SV := isClosed_le (continuous_norm.comp hν) continuous_const
  obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm F
  have hc0 : 0 < ‖c‖ := lt_trans zero_lt_one hc
  set K := {v : Fin d → F | 1 / ‖c‖ ≤ ‖v‖ ∧ ‖v‖ ≤ 1}
  have hKcompact : IsCompact K := by
    refine (isCompact_closedBall (0 : Fin d → F) 1).of_isClosed_subset ?_ ?_
    · exact (isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const)
    · intro v hv
      simpa using hv.2
  have hbounded : ∃ R, SV ⊆ Metric.closedBall 0 R := by
    rcases K.eq_empty_or_nonempty with hK | hK
    · refine ⟨0, fun v _ => ?_⟩
      by_contra hv0
      have hv : v ≠ 0 := fun h => hv0 (by simp [h])
      obtain ⟨n, -, hlt, hge, -⟩ := rescale_to_shell_zpow hc zero_lt_one hv
      have : c ^ n • v ∈ K := ⟨by simpa using hge, hlt.le⟩
      rw [hK] at this
      exact this
    · obtain ⟨v₀, hv₀K, hv₀min⟩ :=
        hKcompact.exists_isMinOn hK (continuous_norm.comp hν).continuousOn
      set m := ‖ν v₀‖
      have hv₀ne : v₀ ≠ 0 := by
        intro h
        have := hv₀K.1
        rw [h, norm_zero] at this
        exact absurd this (not_le.mpr (by positivity))
      have hm : 0 < m := norm_pos_iff.mpr fun h => hv₀ne (hνzero v₀ h)
      refine ⟨max 1 (M / m), fun v hv => ?_⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      by_cases hv0 : v = 0
      · simp [hv0]
      obtain ⟨n, hcn, hlt, hge, -⟩ := rescale_to_shell_zpow hc zero_lt_one hv0
      have hsK : c ^ n • v ∈ K := ⟨by simpa using hge, hlt.le⟩
      have hmin : m ≤ ‖ν (c ^ n • v)‖ := hv₀min hsK
      rw [hνsmul, norm_mul, norm_pow] at hmin
      have hcnpos : 0 < ‖c ^ n‖ := norm_pos_iff.mpr hcn
      set r := ‖c ^ n‖⁻¹
      have hrpos : 0 < r := inv_pos.mpr hcnpos
      have hvr : ‖v‖ ≤ r := by
        have h1 : ‖v‖ = r * ‖c ^ n • v‖ := by
          rw [norm_smul, ← mul_assoc, inv_mul_cancel₀ hcnpos.ne', one_mul]
        rw [h1]
        exact mul_le_of_le_one_right hrpos.le hlt.le
      have hMv : ‖ν v‖ ≤ M := hv
      have hrd : r ^ d * m ≤ M := by
        have hcd : 0 < ‖c ^ n‖ ^ d := pow_pos hcnpos d
        have : m ≤ ‖c ^ n‖ ^ d * M :=
          hmin.trans (mul_le_mul_of_nonneg_left hMv hcd.le)
        calc r ^ d * m ≤ r ^ d * (‖c ^ n‖ ^ d * M) :=
              mul_le_mul_of_nonneg_left this (pow_pos hrpos d).le
          _ = M := by
              rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hcnpos.ne', one_pow, one_mul]
      by_cases hr1 : r ≤ 1
      · exact (hvr.trans hr1).trans (le_max_left _ _)
      · push Not at hr1
        have hrr : r ≤ r ^ d := by
          calc r = r ^ 1 := (pow_one r).symm
            _ ≤ r ^ d := pow_le_pow_right₀ hr1.le hdpos
        have : r ^ d ≤ M / m := by
          rw [le_div_iff₀ hm]
          exact hrd
        exact (hvr.trans (hrr.trans this)).trans (le_max_right _ _)
  obtain ⟨R, hR⟩ := hbounded
  have hSVcompact : IsCompact SV :=
    (isCompact_closedBall (0 : Fin d → F) R).of_isClosed_subset hSVclosed hR
  have himage : {x : E | ‖Algebra.norm F x‖ ≤ M} = e.symm '' SV := by
    ext x
    constructor
    · intro hx
      refine ⟨e x, ?_, e.symm_apply_apply x⟩
      change ‖Algebra.norm F (e.symm (e x))‖ ≤ M
      rw [e.symm_apply_apply]
      exact hx
    · rintro ⟨v, hv, rfl⟩
      exact hv
  rw [himage]
  exact hSVcompact.image e.symm.continuous

/-- Elements of norm one form a compact set. -/
theorem isCompact_algebraNorm_eq_one : IsCompact {x : E | ‖Algebra.norm F x‖ = 1} :=
  (isCompact_algebraNorm_le (F := F) (E := E) 1).of_isClosed_subset
    (isClosed_eq (continuous_norm.comp (continuous_algebraNorm (F := F) (E := E)))
      continuous_const)
    fun _ hx => le_of_eq hx

/-- Units of norm one form a compact subset of the unit group. -/
theorem isCompact_units_algebraNorm_eq_one :
    IsCompact {u : Eˣ | ‖Algebra.norm F (u : E)‖ = 1} := by
  have : T2Space E := t2Space_of_moduleTopology (F := F)
  have : IsTopologicalRing E := IsModuleTopology.isTopologicalRing F E
  set K := {x : E | ‖Algebra.norm F x‖ = 1}
  have hK : IsCompact K := isCompact_algebraNorm_eq_one (F := F) (E := E)
  have hKK : IsCompact (K ×ˢ (MulOpposite.op '' K)) :=
    hK.prod (hK.image MulOpposite.continuous_op)
  have hpre := (Units.isClosedEmbedding_embedProduct (α := E)).isCompact_preimage hKK
  refine hpre.of_isClosed_subset ?_ ?_
  · exact isClosed_eq
      (continuous_norm.comp ((continuous_algebraNorm (F := F) (E := E)).comp Units.continuous_val))
      continuous_const
  · intro u hu
    refine ⟨hu, ⟨((u⁻¹ : Eˣ) : E), ?_, rfl⟩⟩
    change ‖Algebra.norm F ((u⁻¹ : Eˣ) : E)‖ = 1
    have h1 : Algebra.norm F (u : E) * Algebra.norm F ((u⁻¹ : Eˣ) : E) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have h2 := congrArg norm h1
    rw [norm_mul, norm_one, hu, one_mul] at h2
    exact h2

end Langlands.Plancherel.TorusNormKernel

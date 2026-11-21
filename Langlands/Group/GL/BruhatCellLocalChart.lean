import Langlands.Group.GL.BruhatCellMatrixSlice
import Langlands.Group.GL.BruhatTransverseChart
import Mathlib.Topology.OpenPartialHomeomorph.IsImage

/-! # Local smooth charts identifying the actual Bruhat cell with a slice -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

open Function Set Filter
open scoped ContDiff Matrix.Norms.Operator Topology

namespace Langlands.GeneralLinear

universe u

variable {F : Type u} [RCLike F] {n : ℕ} (w : Equiv.Perm (Fin n))

local notation "M" => Matrix (Fin n) (Fin n) F
local notation "B" => upperTriangularSubgroup n F
local notation "V" => permutationUnipotentMinus n F w
local notation "P" => permutation n F w
local notation "T" => (bruhatUpperSpace F n × bruhatInversionSpace F w)
local notation "Nspace" => bruhatNormalSpace F w
local notation "W[" S "]" => (T × (↥S) × ℝ)

/-- At the given cell point, restrict the straightened chart so that
its target lies in the prescribed neighborhood and the zero normal
slice agrees with the actual cell throughout the chart. -/
theorem exists_bruhatCellLocalChart (g : B) (v : V) (N : Nspace) (hN : N ≠ 0)
    {O : Set M} (hO : IsOpen O) (h0 : g.val.val * (P * v.val).val ∈ O) :
    ∃ (Y : Type u) (norm : NormedAddCommGroup Y),
      letI : NormedAddCommGroup Y := norm
      ∃ space : NormedSpace ℝ Y,
      letI : NormedSpace ℝ Y := space
      ∃ (_ : FiniteDimensional ℝ Y) (q : OpenPartialHomeomorph (T × Y × ℝ) M),
      q 0 = g.val.val * (P * v.val).val ∧ 0 ∈ q.source ∧ q.target ⊆ O ∧
      ContDiffOn ℝ ∞ q q.source ∧ ContDiffOn ℝ ∞ q.symm q.target ∧
      (∀ z ∈ q.source, q z ∈ bruhatCellMatrixSet F w ↔ z.2 = 0) ∧
      ∀ z ∈ q.source, fderiv ℝ q z (0, 0, 1) = N.val * q z := by
  obtain ⟨S, e, heq, he₀, heInv⟩ :=
    exists_bruhatStraightenedChart (F := F) (w := w) g (P * v.val) N hN
  have heSlice (z : T) : e (z, 0) = bruhatCellMatrixParam (w := w) g (P * v.val) z :=
    (congrFun heq (z, 0)).trans
      (bruhatStraightenedMatrixParam_slice (F := F) (w := w) S g (P * v.val) N z)
  have he0 : e (0 : W[S]) = g.val.val * (P * v.val).val :=
    (heSlice 0).trans (bruhatCellMatrixParam_zero (w := w) g (P * v.val))
  have heSmooth : ContDiff ℝ ∞ (e : W[S] → M) := by
    rw [heq]
    exact contDiff_bruhatStraightenedMatrixParam (F := F) (w := w) S g (P * v.val) N
  have hloc : ∀ᶠ z : W[S] in 𝓝 0, e z ∈ bruhatCellMatrixSet F w ↔ z.2 = 0 :=
    eventually_mem_bruhatCellMatrixSet_iff w g v e he₀ heSlice
  obtain ⟨Q, hQsub, hQo, hQ₀⟩ := mem_nhds_iff.mp hloc
  let U := Q ∩ e ⁻¹' O
  have hU : IsOpen U := hQo.inter (hO.preimage heSmooth.continuous)
  let q := e.restrOpen U hU
  have hq₀ : 0 ∈ q.source := by
    refine ⟨he₀, hQ₀, ?_⟩
    change e (0 : W[S]) ∈ O
    rwa [he0]
  have hqO : q.target ⊆ O := by
    intro y hy
    have hx : q.symm y ∈ q.source := q.map_target hy
    have hy' : q (q.symm y) ∈ O := hx.2.2
    rwa [q.right_inv hy] at hy'
  have : FiniteDimensional ℝ Nspace := FiniteDimensional.trans ℝ F Nspace
  refine ⟨↥S, inferInstance, inferInstance, inferInstance, q, he0, hq₀, hqO,
    heSmooth.contDiffOn, heInv.mono (fun _ hz => hz.1),
    fun z hz => hQsub hz.2.1, ?_⟩
  intro z _
  change fderiv ℝ e z (0, 0, 1) = N.val * e z
  rw [heq, fderiv_bruhatStraightenedMatrixParam_last]

end Langlands.GeneralLinear

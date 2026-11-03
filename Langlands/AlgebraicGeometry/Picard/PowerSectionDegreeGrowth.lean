import Langlands.AlgebraicGeometry.Picard.PositiveTensorPowerAmpleProof

/-! # Increasing section degrees without changing generation opens -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.SchemeModule Langlands.Scheme.Modules

namespace Langlands.AlgebraicGeometry.Picard.LineBundle

variable {X : Scheme.{u}} (L : LineBundle X)

/-- Raise a section of `Lⁿ` to its `k`-th power and transport it to the
specified actual tensor power `Lⁿᵏ`. -/
def multiplySectionDegree {n : ℕ} (s : L.powSections n) (k : ℕ) :
    L.powSections (n * k) :=
  (tensorPowMulIso L.obj n k).hom.app ⊤
    (sectionPow (tensorPow L.obj n) s k)

/-- Raising a section to a positive power preserves its whole generation open. -/
theorem sectionOpen_multiplySectionDegree {n : ℕ}
    (s : L.powSections n) {k : ℕ} (hk : 0 < k) :
    L.sectionOpen (L.multiplySectionDegree s k) = L.sectionOpen s := by
  change trivializationOpen _ ((tensorPowMulIso L.obj n k).hom.app ⊤ _) = _
  rw [trivializationOpen_mapIso]
  exact trivializationOpen_sectionPow
    ⟨tensorPow L.obj n, tensorPow_isLocallyFreeRankOne X L n⟩ s hk

/-- Every family of sections in one positive degree can be moved to a common
degree above any specified threshold, preserving every generation open.
The family need not be finite. -/
theorem exists_sections_above_degree {ι : Type*} {n : ℕ} (hn : 0 < n)
    (s : ι → L.powSections n) (N : ℕ) :
    ∃ m : ℕ, 0 < m ∧ N ≤ m ∧ ∃ t : ι → L.powSections m,
      ∀ i, L.sectionOpen (t i) = L.sectionOpen (s i) := by
  refine ⟨n * (N + 1), Nat.mul_pos hn (Nat.succ_pos _), ?_,
    fun i ↦ L.multiplySectionDegree (s i) (N + 1), fun i ↦
      L.sectionOpen_multiplySectionDegree (s i) (Nat.succ_pos _)⟩
  calc
    N ≤ N + 1 := Nat.le_succ N
    _ = 1 * (N + 1) := (one_mul _).symm
    _ ≤ n * (N + 1) := Nat.mul_le_mul_right _ hn

end Langlands.AlgebraicGeometry.Picard.LineBundle

import Langlands.HarmonicAnalysis.RectangularFourier
import Langlands.Representation.Smooth.Definitions
import Mathlib.Topology.Algebra.OpenSubgroup

/-! Uniform open right stabilizers of rectangular Schwartz–Bruhat tests. -/

namespace Langlands.HarmonicAnalysis

universe uF

open Set
open scoped Topology

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  {r s : ℕ}

/-- The subgroup fixing a rectangular test under actual right matrix multiplication. -/
def rectangularTestStabilizer (Φ : SchwartzBruhat (Matrix (Fin r) (Fin s) F)) :
    Subgroup (Langlands.GeneralLinear s F) where
  carrier := {g | ∀ M, Φ (M * g.val) = Φ M}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh M
    rw [Units.val_mul, ← Matrix.mul_assoc, hh, hg]
  inv_mem' := by
    intro g hg M
    have h := hg (M * (g⁻¹).val)
    rw [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.mul_one] at h
    exact h.symm

/-- Compact support and local constancy give one open subgroup fixing the whole test. -/
theorem rectangularTestStabilizer_isOpen
    (Φ : SchwartzBruhat (Matrix (Fin r) (Fin s) F)) :
    IsOpen (rectangularTestStabilizer Φ : Set (Langlands.GeneralLinear s F)) := by
  let O : Set (Langlands.GeneralLinear s F × Matrix (Fin r) (Fin s) F) :=
    {p | Φ (p.2 * p.1.val) = Φ p.2}
  have hmul : Continuous (fun p :
      Langlands.GeneralLinear s F × Matrix (Fin r) (Fin s) F => p.2 * p.1.val) :=
    continuous_snd.matrix_mul (Units.continuous_val.comp continuous_fst)
  have hO : IsOpen O :=
    ((Φ.locallyConstant.comp_continuous hmul).prodMk
      (Φ.locallyConstant.comp_continuous continuous_snd)) {p : ℂ × ℂ | p.1 = p.2}
  have hsubset : ({1} : Set (Langlands.GeneralLinear s F)) ×ˢ
      tsupport (Φ : Matrix (Fin r) (Fin s) F → ℂ) ⊆ O := by
    rintro ⟨g, M⟩ ⟨hg, _⟩
    rcases Set.mem_singleton_iff.mp hg with rfl
    simp [O]
  obtain ⟨U, W, hU, _, h1U, hsW, hUW⟩ :=
    generalized_tube_lemma isCompact_singleton Φ.hasCompactSupport hO hsubset
  have h1 : (1 : Langlands.GeneralLinear s F) ∈ U := h1U (by simp)
  have hinvU : IsOpen ((fun g : Langlands.GeneralLinear s F => g⁻¹) ⁻¹' U) :=
    hU.preimage continuous_inv
  apply (rectangularTestStabilizer Φ).isOpen_of_mem_nhds (g := 1)
  apply Filter.mem_of_superset ((hU.inter hinvU).mem_nhds ⟨h1, by simpa using h1⟩)
  intro g hg
  change ∀ M, Φ (M * g.val) = Φ M
  intro M
  by_cases hM : M ∈ tsupport (Φ : Matrix (Fin r) (Fin s) F → ℂ)
  · exact hUW (show (g, M) ∈ U ×ˢ W from ⟨hg.1, hsW hM⟩)
  · have hM0 : Φ M = 0 := image_eq_zero_of_notMem_tsupport hM
    by_cases hN : M * g.val ∈ tsupport (Φ : Matrix (Fin r) (Fin s) F → ℂ)
    · have hi := hUW (show (g⁻¹, M * g.val) ∈ U ×ˢ W from ⟨hg.2, hsW hN⟩)
      change Φ (M * g.val * (g⁻¹).val) = Φ (M * g.val) at hi
      rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.mul_one] at hi
      exact hi.symm
    · exact (image_eq_zero_of_notMem_tsupport hN).trans hM0.symm

/-- Rectangular Schwartz–Bruhat tests have uniform open right stabilizers. -/
theorem rectangularTestSmooth (Φ : SchwartzBruhat (Matrix (Fin r) (Fin s) F)) :
    ∃ U : OpenSubgroup (Langlands.GeneralLinear s F),
      ∀ g ∈ U, ∀ M : Matrix (Fin r) (Fin s) F, Φ (M * g.val) = Φ M :=
  ⟨⟨rectangularTestStabilizer Φ, rectangularTestStabilizer_isOpen Φ⟩, fun _ hg => hg⟩

/-- The existing right-translation representation on rectangular tests is smooth. -/
theorem rectangularSchwartzRepresentation_isSmooth :
    IsSmooth (rectangularSchwartzRepresentation (K := F) (r := r) (s := s)) := by
  intro Φ
  obtain ⟨U, hU⟩ := rectangularTestSmooth Φ
  refine ⟨U, ?_⟩
  intro g
  ext M
  exact hU g g.property M

end Langlands.HarmonicAnalysis

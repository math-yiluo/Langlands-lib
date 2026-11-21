import Langlands.HarmonicAnalysis.Distribution.ZeroSectionFieldVanishing

/-! # Flattening finite jets by iterating a vanishing vector field -/

noncomputable section

open Set TopologicalSpace
open scoped ContDiff Distributions

set_option autoImplicit false

namespace Langlands.HarmonicAnalysis

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {Ω : Opens E} {W : E → E} {b : E → ℝ}

private theorem shiftedField_leadingJet (hW : ContDiffOn ℝ ∞ W Ω) (hb : ContDiffOn ℝ ∞ b Ω)
    (f : 𝓓(Ω, ℝ)) {x : E} (hx : x ∈ Ω) (hWx : W x = 0) (hbx : b x = 0)
    (k : ℕ) (hf : ∀ j < k, iteratedFDeriv ℝ j f x = 0) :
    iteratedFDeriv ℝ k (shiftedVectorFieldDerivativeTest hW hb f) x =
      jetSlotSum k (fderiv ℝ W x) (iteratedFDeriv ℝ k f x) := by
  let g := smoothVectorFieldDerivativeTest hW f
  let h := localScalarMultiplierCLM hb f
  have hg : ContDiffAt ℝ k g x := g.contDiff.contDiffAt.of_le (by simp)
  have hh : ContDiffAt ℝ k h x := h.contDiff.contDiffAt.of_le (by simp)
  change iteratedFDeriv ℝ k ((g : E → ℝ) + (h : E → ℝ)) x = _
  rw [iteratedFDeriv_add_apply hg hh]
  change iteratedFDeriv ℝ k (fun y => fderiv ℝ f y (W y)) x +
    iteratedFDeriv ℝ k (fun y => f y * b y) x = _
  rw [iteratedFDeriv_vectorField_of_eq_zero Ω.isOpen f.contDiff hW hx hWx k hf,
    iteratedFDeriv_mul_eq_zero_of_lower_eq_zero Ω.isOpen f.contDiff hb hx hbx k hf, add_zero]

private theorem iterate_shiftedField_jet (hW : ContDiffOn ℝ ∞ W Ω) (hb : ContDiffOn ℝ ∞ b Ω)
    (f : 𝓓(Ω, ℝ)) {x : E} (hx : x ∈ Ω) (hWx : W x = 0) (hbx : b x = 0)
    {k : ℕ} (hflat : ∀ j < k, iteratedFDeriv ℝ j f x = 0) (p : ℕ) (j : ℕ) (hj : j ≤ k) :
    iteratedFDeriv ℝ j ((shiftedVectorFieldDerivativeTest hW hb)^[p] f) x =
      (jetSlotSum j (fderiv ℝ W x) ^ p) (iteratedFDeriv ℝ j f x) := by
  induction p generalizing j with
  | zero => simp
  | succ p ih =>
    rw [Function.iterate_succ_apply']
    have hlow (i : ℕ) (hi : i < j) :
        iteratedFDeriv ℝ i ((shiftedVectorFieldDerivativeTest hW hb)^[p] f) x = 0 := by
      rw [ih i (hi.le.trans hj), hflat i (hi.trans_le hj), map_zero]
    rw [shiftedField_leadingJet hW hb _ hx hWx hbx j hlow, ih j hj, pow_succ', Module.End.mul_apply]

/-- A sufficiently high power of a vector field vanishing and linearized
nilpotently on a set sends every test to a test flat through any prescribed order there. -/
theorem exists_iterate_shiftedField_flat (hW : ContDiffOn ℝ ∞ W Ω) (hb : ContDiffOn ℝ ∞ b Ω)
    {Z : Set E} (hZ : Z ⊆ Ω) (hWb : ∀ x ∈ Z, W x = 0 ∧ b x = 0)
    (hNil : ∀ x ∈ Z, IsNilpotent (fderiv ℝ W x).toLinearMap) (k : ℕ) :
    ∃ p : ℕ, ∀ (f : 𝓓(Ω, ℝ)) (x : E), x ∈ Z → ∀ j < k,
      iteratedFDeriv ℝ j ((shiftedVectorFieldDerivativeTest hW hb)^[p] f) x = 0 := by
  induction k with
  | zero => exact ⟨0, fun _ _ _ _ hj => (Nat.not_lt_zero _ hj).elim⟩
  | succ k ih =>
    obtain ⟨p, hp⟩ := ih
    let q := k * Module.finrank ℝ E + 1
    refine ⟨q + p, fun f x hx j hj => ?_⟩
    let g := (shiftedVectorFieldDerivativeTest hW hb)^[p] f
    rw [Function.iterate_add_apply]
    have hg : ∀ l < k, iteratedFDeriv ℝ l g x = 0 := hp f x hx
    rw [iterate_shiftedField_jet hW hb g (hZ hx) (hWb x hx).1 (hWb x hx).2
      hg q j (Nat.le_of_lt_succ hj)]
    rcases (Nat.le_of_lt_succ hj).lt_or_eq with hjk | rfl
    · rw [hg j hjk, map_zero]
    · rw [show (jetSlotSum (F := ℝ) j (fderiv ℝ W x)) ^ q = 0 from
        jetSlotSum_finrank_pow_eq_zero j _ (hNil x hx), LinearMap.zero_apply]

/-- Uniform flattening of finite jets for iterated shifted field derivatives. -/
def VanishingFieldJetFlatteningStatement : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Ω : Opens E) (W : E → E) (b : E → ℝ) (Z : Set E), Z ⊆ Ω →
    (∀ x ∈ Z, W x = 0 ∧ b x = 0) → (∀ x ∈ Z, IsNilpotent (fderiv ℝ W x).toLinearMap) →
    ∀ (hW : ContDiffOn ℝ ∞ W Ω) (hb : ContDiffOn ℝ ∞ b Ω) (k : ℕ),
    ∃ p : ℕ, ∀ (f : 𝓓(Ω, ℝ)) (x : E), x ∈ Z → ∀ j < k,
      iteratedFDeriv ℝ j ((shiftedVectorFieldDerivativeTest hW hb)^[p] f) x = 0

theorem vanishingFieldJetFlattening : VanishingFieldJetFlatteningStatement.{u} := by
  intro E _ _ _ Ω W b Z hZ hWb hNil hW hb k
  exact exists_iterate_shiftedField_flat hW hb hZ hWb hNil k

end Langlands.HarmonicAnalysis

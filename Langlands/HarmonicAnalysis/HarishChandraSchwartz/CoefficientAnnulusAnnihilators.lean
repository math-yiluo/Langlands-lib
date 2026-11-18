import Langlands.HarmonicAnalysis.HarishChandraSchwartz.FixedLevelCoefficientAnnihilators
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RecurrenceTailBound

/-! # Invertible annihilators from a fixed-level spectral annulus -/

noncomputable section

namespace Langlands.HarishChandraSchwartz

open Polynomial

/-- A monic polynomial with every root bounded away from zero has its
constant coefficient bounded away from zero by the corresponding power. -/
theorem pow_le_norm_coeff_zero_of_roots {p : ℂ[X]} (hp : p.Monic)
    {η : ℝ} (hη : 0 ≤ η) (hroots : ∀ z ∈ p.roots, η ≤ ‖z‖) :
    η ^ p.natDegree ≤ ‖p.coeff 0‖ := by
  have hcard : Multiset.card p.roots = p.natDegree := IsAlgClosed.card_roots_eq_natDegree
  rw [coeff_zero_eq_eval_zero]
  conv_rhs => rw [← prod_multiset_X_sub_C_of_monic_of_roots_card_eq hp hcard]
  rw [eval_multiset_prod, Multiset.map_map]
  have h := pow_le_norm_multiset_prod
    (t := p.roots.map (eval 0 ∘ fun z => X - C z)) hη ?_
  · rwa [Multiset.card_map, hcard] at h
  · intro z hz
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hz
    simpa only [Function.comp_apply, eval_sub, eval_X, eval_C, zero_sub, norm_neg]
      using hroots w hw

universe uM uA uY

variable {M : Type uM} [Group M] {A : Type uA} [CommGroup A]
  {Y : Type uY} [AddCommGroup Y] [Module ℂ Y]

/-- A right-translation annihilator with a degree and coefficient bound and
a lower bound on the norm of its constant coefficient. -/
abbrev HasBoundedRightAnnihilator (a : M) (F : M → ℂ) (d : ℕ) (B α : ℝ) : Prop :=
  ∃ p : ℂ[X], IsCoeffBounded p d B ∧ α ≤ ‖p.coeff 0‖ ∧
    aeval (HarmonicAnalysis.GroupAction.rightFunctions a) p F = 0

/-- A coefficient sum from a stable space of dimension at most `d`, whose
occurring exponent values lie in `η ≤ norm ≤ Λ`, has a uniformly bounded
annihilator with constant coefficient at least `η^(d*d)`. No padding by zero
roots is used. -/
theorem exists_annulus_bounded_coefficient_annihilator
    (J : Representation ℂ M Y) (j : A →* M) (a : A)
    (W : Submodule ℂ Y) [FiniteDimensional ℂ W]
    (hW : ∀ a, ∀ y ∈ W, J (j a) y ∈ W) {d : ℕ} (hd : Module.finrank ℂ W ≤ d)
    {η Λ : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) (hΛ : 1 ≤ Λ)
    (hroots : ∀ χ, W ⊓ jointGenEigenspace (J.comp j) χ ≠ ⊥ →
      η ≤ ‖χ a‖ ∧ ‖χ a‖ ≤ Λ)
    {F : M → ℂ} (hF : F ∈ coefficientSpaceFrom J W) :
    HasBoundedRightAnnihilator (j a) F (d * d) (2 ^ (d * d) * Λ ^ (d * d))
      (η ^ (d * d)) := by
  classical
  obtain ⟨s, c, hs, hc, hk, hexp, hsum⟩ :=
    exists_bounded_coefficient_eigenfunctions J j a W hW hd hF
  let p : ℂ[X] := ∏ χ ∈ s, (X - C (χ a)) ^ d
  have hp : p.Monic := monic_prod_of_monic _ _ fun _ _ => (monic_X_sub_C _).pow _
  have hdeg : p.natDegree ≤ d * d := by
    dsimp only [p]
    rw [natDegree_prod_of_monic _ _ (fun _ _ => (monic_X_sub_C _).pow _)]
    simp only [natDegree_pow, natDegree_X_sub_C, mul_one, Finset.sum_const, nsmul_eq_mul]
    exact Nat.mul_le_mul_right d hs
  have hpr : ∀ z ∈ p.roots, η ≤ ‖z‖ ∧ ‖z‖ ≤ Λ := by
    intro z hz
    obtain ⟨χ, hχ, rfl⟩ := exists_eq_of_mem_roots_prod hz
    exact hroots χ (hexp χ hχ)
  have hpb := isCoeffBounded_of_roots hp hΛ (fun z hz => (hpr z hz).2)
  refine ⟨p, ⟨hdeg, fun k => (hpb.2 k).trans ?_⟩, ?_, ?_⟩
  · exact mul_le_mul (pow_le_pow_right₀ (by norm_num) hdeg)
      (pow_le_pow_right₀ hΛ hdeg) (by positivity) (by positivity)
  · exact (pow_le_pow_of_le_one hη0.le hη1 hdeg).trans
      (pow_le_norm_coeff_zero_of_roots hp hη0.le (fun z hz => (hpr z hz).1))
  · rw [← hsum]
    apply aeval_prod_apply_sum_eq_zero
    intro χ hχ
    rw [map_pow, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]
    exact hk χ hχ

/-- The same annulus yields an explicit common bound by any prescribed
finite forward tail of the actual coefficient function. -/
theorem norm_le_sum_tail_of_coefficient_annulus
    (J : Representation ℂ M Y) (j : A →* M) (a : A)
    (W : Submodule ℂ Y) [FiniteDimensional ℂ W]
    (hW : ∀ a, ∀ y ∈ W, J (j a) y ∈ W) {d : ℕ} (hd : Module.finrank ℂ W ≤ d)
    {η Λ : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) (hΛ : 1 ≤ Λ)
    (hroots : ∀ χ, W ⊓ jointGenEigenspace (J.comp j) χ ≠ ⊥ →
      η ≤ ‖χ a‖ ∧ ‖χ a‖ ≤ Λ)
    {F : M → ℂ} (hF : F ∈ coefficientSpaceFrom J W) (r : ℕ) (m : M) :
    ‖F m‖ ≤
      (((d * d + 1 : ℕ) : ℝ) * ((η ^ (d * d))⁻¹ * (2 ^ (d * d) * Λ ^ (d * d)))) ^ r *
        ∑ i ∈ Finset.range (r * (d * d) + 1), ‖F (m * (j a) ^ (r + i))‖ := by
  obtain ⟨p, hp, hp0, hann⟩ :=
    exists_annulus_bounded_coefficient_annihilator J j a W hW hd hη0 hη1 hΛ hroots hF
  exact norm_le_sum_tail_of_aeval_eq_zero (j a) (d * d) r (pow_pos hη0 _) hp hp0 hann m

end Langlands.HarishChandraSchwartz

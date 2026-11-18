import Langlands.HarmonicAnalysis.HarishChandraSchwartz.UniformExponentAnnihilators

/-! # Uniform annihilators without fixed exponent labels -/

noncomputable section

namespace Langlands.HarishChandraSchwartz

open Polynomial Langlands.HarmonicAnalysis
open scoped NNReal

/-- Pad a polynomial up to a prescribed degree using a specified extra root. -/
def padPolynomialDegree (p : ℂ[X]) (N : ℕ) (z : ℂ) : ℂ[X] :=
  (X - C z) ^ (N - p.natDegree) * p

theorem padPolynomialDegree_monic {p : ℂ[X]} (hp : p.Monic) (N : ℕ) (z : ℂ) :
    (padPolynomialDegree p N z).Monic :=
  ((monic_X_sub_C z).pow _).mul hp

theorem natDegree_padPolynomialDegree {p : ℂ[X]} (hp : p.Monic) {N : ℕ}
    (hN : p.natDegree ≤ N) (z : ℂ) : (padPolynomialDegree p N z).natDegree = N := by
  rw [padPolynomialDegree, natDegree_mul (pow_ne_zero _ (X_sub_C_ne_zero _)) hp.ne_zero,
    natDegree_pow, natDegree_X_sub_C, mul_one, Nat.sub_add_cancel hN]

theorem roots_padPolynomialDegree {p : ℂ[X]} (hp : p.Monic) (N : ℕ) (z : ℂ)
    {w : ℂ} (hw : w ∈ (padPolynomialDegree p N z).roots) : w = z ∨ w ∈ p.roots := by
  rw [mem_roots (padPolynomialDegree_monic hp N z).ne_zero, IsRoot.def,
    padPolynomialDegree, eval_mul, mul_eq_zero] at hw
  rcases hw with hw | hw
  · left
    rw [eval_pow, eval_sub, eval_X, eval_C] at hw
    by_cases hn : N - p.natDegree = 0
    · simp [hn] at hw
    · exact sub_eq_zero.mp ((pow_eq_zero_iff hn).mp hw)
  · right
    exact (mem_roots hp.ne_zero).mpr hw

theorem aeval_padPolynomialDegree_eq_zero {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    (T : Module.End ℂ Y) {p : ℂ[X]} (N : ℕ) (z : ℂ) {y : Y}
    (h : aeval T p y = 0) : aeval T (padPolynomialDegree p N z) y = 0 := by
  rw [padPolynomialDegree, map_mul, Module.End.mul_apply, h, map_zero]

/-- Distinct simultaneous generalized eigencomponents in a finite-dimensional
space have support cardinality bounded by the dimension of that space. -/
theorem support_card_le_finrank_of_jointGenEigenspace
    {A : Type*} [CommGroup A] {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    (T : A →* Module.End ℂ Y) (W : Submodule ℂ Y) [FiniteDimensional ℂ W]
    (c : (A → ℂ) →₀ Y) (hc : ∀ χ, c χ ∈ W ⊓ jointGenEigenspace T χ) :
    c.support.card ≤ Module.finrank ℂ W := by
  classical
  let v : c.support → W := fun χ => ⟨c χ, (hc χ).1⟩
  have hv : LinearIndependent ℂ (fun χ : c.support => c χ) :=
    ((iSupIndep_jointGenEigenspace T).comp Subtype.val_injective).linearIndependent _
      (fun χ => (hc χ).2) (fun χ => Finsupp.mem_support_iff.mp χ.property)
  have hvW : LinearIndependent ℂ v := LinearIndependent.of_comp W.subtype hv
  simpa only [Fintype.card_coe] using hvW.fintype_card_le_finrank

variable {M : Type*} [Group M] {A : Type*} [CommGroup A] {κ ι : Type*}

/-- A bounded number of generalized eigenfunctions with a uniform nilpotence
order and nonunitary root bound yields fixed-degree annihilators of the actual
weak and positive parts. Labels, their cardinality, and their unitary classification
may all vary with the parameter. -/
theorem hasUniformSplitAnnihilators_of_variable_eigenfunctions
    (j : A →* M) (a : A) (s : κ → Finset ι) (χ : κ → ι → A → ℂ)
    (c : κ → ι → M → ℂ) (n d : ℕ) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hs : ∀ ω, (s ω).card ≤ n)
    (hc : ∀ ω i, i ∈ s ω →
      c ω i ∈ jointGenEigenspace (componentRightTranslation j) (χ ω i))
    (hk : ∀ ω i, i ∈ s ω →
      ((componentRightTranslation j a - χ ω i a • 1) ^ d) (c ω i) = 0)
    (hbound : ∀ ω i, i ∈ s ω → χ ω i ∉ unitaryExponents A → ‖χ ω i a‖ ≤ θ) :
    HasUniformSplitAnnihilators j a (fun ω => ∑ i ∈ s ω, c ω i) := by
  classical
  let sw := fun ω => (s ω).filter (fun i => χ ω i ∈ unitaryExponents A)
  let sp := fun ω => (s ω).filter (fun i => χ ω i ∉ unitaryExponents A)
  let pw := fun ω => ∏ i ∈ sw ω, (X - C (χ ω i a)) ^ d
  let pp := fun ω => ∏ i ∈ sp ω, (X - C (χ ω i a)) ^ d
  have hpw : ∀ ω, (pw ω).Monic := fun _ =>
    monic_prod_of_monic _ _ fun _ _ => (monic_X_sub_C _).pow _
  have hpp : ∀ ω, (pp ω).Monic := fun _ =>
    monic_prod_of_monic _ _ fun _ _ => (monic_X_sub_C _).pow _
  have hdeg (ω : κ) (t : Finset ι) (ht : t ⊆ s ω) :
      (∏ i ∈ t, (X - C (χ ω i a)) ^ d).natDegree ≤ n * d := by
    rw [natDegree_prod_of_monic _ _ (fun _ _ => (monic_X_sub_C _).pow _)]
    simp only [natDegree_pow, natDegree_X_sub_C, mul_one, Finset.sum_const, nsmul_eq_mul]
    exact Nat.mul_le_mul_right d ((Finset.card_le_card ht).trans (hs ω))
  have hdw : ∀ ω, (pw ω).natDegree ≤ n * d := fun ω => hdeg ω _ (Finset.filter_subset _ _)
  have hdp : ∀ ω, (pp ω).natDegree ≤ n * d := fun ω => hdeg ω _ (Finset.filter_subset _ _)
  have hann : ∀ ω (t : Finset ι), t ⊆ s ω →
      aeval (GroupAction.rightFunctions (j a)) (∏ i ∈ t, (X - C (χ ω i a)) ^ d)
        (∑ i ∈ t, c ω i) = 0 := by
    intro ω t ht
    refine aeval_prod_apply_sum_eq_zero _ _ _ _ fun i hi => ?_
    rw [map_pow, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]
    exact hk ω i (ht hi)
  refine ⟨n * d, n * d, θ, (fun ω => padPolynomialDegree (pw ω) (n * d) 1),
    (fun ω => padPolynomialDegree (pp ω) (n * d) 0), hθ0, hθ1,
    (fun ω => padPolynomialDegree_monic (hpw ω) _ _),
    (fun ω => padPolynomialDegree_monic (hpp ω) _ _),
    (fun ω => natDegree_padPolynomialDegree (hpw ω) (hdw ω) _),
    (fun ω => natDegree_padPolynomialDegree (hpp ω) (hdp ω) _), ?_, ?_, ?_, ?_⟩
  · intro ω z hz
    rcases roots_padPolynomialDegree (hpw ω) _ _ hz with rfl | hz
    · exact norm_one
    · obtain ⟨i, hi, rfl⟩ := exists_eq_of_mem_roots_prod hz
      exact (Finset.mem_filter.mp hi).2 a
  · intro ω z hz
    rcases roots_padPolynomialDegree (hpp ω) _ _ hz with rfl | hz
    · simpa only [norm_zero] using hθ0
    · obtain ⟨i, hi, rfl⟩ := exists_eq_of_mem_roots_prod hz
      obtain ⟨his, hiU⟩ := Finset.mem_filter.mp hi
      exact hbound ω i his hiU
  · intro ω
    rw [weakPart_sum_labels j (s ω) (χ ω) (c ω) (hc ω)
      (fun i => χ ω i ∈ unitaryExponents A) (fun _ _ => Iff.rfl)]
    exact aeval_padPolynomialDegree_eq_zero _ _ _ (hann ω _ (Finset.filter_subset _ _))
  · intro ω
    rw [positivePart_sum_labels j (s ω) (χ ω) (c ω) (hc ω)
      (fun i => χ ω i ∈ unitaryExponents A) (fun _ _ => Iff.rfl)]
    exact aeval_padPolynomialDegree_eq_zero _ _ _ (hann ω _ (Finset.filter_subset _ _))

end Langlands.HarishChandraSchwartz

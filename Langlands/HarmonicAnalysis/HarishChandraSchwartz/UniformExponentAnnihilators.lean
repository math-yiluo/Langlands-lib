import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitPositiveConstantTerm
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.WeakPartProjection

/-!
# Uniform annihilators for labelled exponent families

This internal bridge isolates the finite-label polynomial step in Waldspurger's proof of
VI.2.3, printed p.300. Labels, their multiplicities and their unitary classification are fixed,
while the eigenvalue functions and generalized eigenfunctions may depend on a parameter.
Different labels may have the same specialized eigenvalue function.
-/

noncomputable section

namespace Langlands.HarishChandraSchwartz

open Polynomial Langlands.HarmonicAnalysis

variable {M : Type*} [Group M] {A : Type*} [CommGroup A] {κ ι : Type*}

/-- The existing weak and positive parts of a function family have monic annihilators of
parameter-independent degrees, with unitary weak roots and a uniform positive root bound
strictly below one, for right translation by `j a`. -/
def HasUniformSplitAnnihilators (j : A →* M) (a : A) (F : κ → M → ℂ) : Prop :=
  ∃ (Nw Np : ℕ) (θ : ℝ) (pw pp : κ → ℂ[X]),
    0 ≤ θ ∧ θ < 1 ∧
    (∀ ω, (pw ω).Monic) ∧ (∀ ω, (pp ω).Monic) ∧
    (∀ ω, (pw ω).natDegree = Nw) ∧ (∀ ω, (pp ω).natDegree = Np) ∧
    (∀ ω, ∀ z ∈ (pw ω).roots, ‖z‖ = 1) ∧
    (∀ ω, ∀ z ∈ (pp ω).roots, ‖z‖ ≤ θ) ∧
    (∀ ω, aeval (GroupAction.rightFunctions (j a)) (pw ω) (weakPart j (F ω)) = 0) ∧
    (∀ ω, aeval (GroupAction.rightFunctions (j a)) (pp ω) (positivePart j (F ω)) = 0)

open Classical in
/-- A labelled finite expansion determines the actual weak part by its unitary labels.
The eigenvalue functions need not be distinct. -/
theorem weakPart_sum_labels (j : A →* M) (s : Finset ι)
    (χ : ι → A → ℂ) (c : ι → M → ℂ)
    (hc : ∀ i ∈ s, c i ∈ jointGenEigenspace (componentRightTranslation j) (χ i))
    (U : ι → Prop) (hU : ∀ i ∈ s, U i ↔ χ i ∈ unitaryExponents A) :
    weakPart j (∑ i ∈ s, c i) = ∑ i ∈ s with U i, c i := by
  classical
  have hw : ∑ i ∈ s with U i, c i ∈ weakExponentSpace j := by
    refine Submodule.sum_mem _ fun i hi => ?_
    obtain ⟨his, hiU⟩ := Finset.mem_filter.mp hi
    exact (le_iSup₂ (f := fun χ (_ : χ ∈ unitaryExponents A) =>
      jointGenEigenspace (componentRightTranslation j) χ) (χ i) ((hU i his).mp hiU))
      (hc i his)
  have hp : ∑ i ∈ s with ¬ U i, c i ∈ positiveExponentSpace j := by
    refine Submodule.sum_mem _ fun i hi => ?_
    obtain ⟨his, hiU⟩ := Finset.mem_filter.mp hi
    have hχ : χ i ∈ (unitaryExponents A)ᶜ := fun h => hiU ((hU i his).mpr h)
    exact (le_iSup₂ (f := fun χ (_ : χ ∈ (unitaryExponents A)ᶜ) =>
      jointGenEigenspace (componentRightTranslation j) χ) (χ i) hχ) (hc i his)
  refine weakPart_eq_of_mem j hw ?_
  rw [← Finset.sum_filter_add_sum_filter_not s U, add_sub_cancel_left]
  exact hp

open Classical in
/-- The actual positive part is the sum over the complementary labels, including when
distinct labels specialize to the same eigenvalue function. -/
theorem positivePart_sum_labels (j : A →* M) (s : Finset ι)
    (χ : ι → A → ℂ) (c : ι → M → ℂ)
    (hc : ∀ i ∈ s, c i ∈ jointGenEigenspace (componentRightTranslation j) (χ i))
    (U : ι → Prop) (hU : ∀ i ∈ s, U i ↔ χ i ∈ unitaryExponents A) :
    positivePart j (∑ i ∈ s, c i) = ∑ i ∈ s with ¬ U i, c i := by
  classical
  rw [positivePart, weakPart_sum_labels j s χ c hc U hU,
    ← Finset.sum_filter_add_sum_filter_not s U, add_sub_cancel_left]

/-- Fixed labels, multiplicities and root bounds give uniform annihilators for the existing
weak and positive parts. No injectivity or generic-parameter assumption is imposed on `χ`.
The fixed power `k i` annihilates the component with label `i` at the chosen element `a`. -/
theorem hasUniformSplitAnnihilators_of_labelled_eigenfunctions (j : A →* M) (a : A)
    (s : Finset ι) (U : ι → Prop) (k : ι → ℕ) (r : ι → NNReal)
    (χ : κ → ι → A → ℂ) (c : κ → ι → M → ℂ)
    (hc : ∀ ω i, i ∈ s →
      c ω i ∈ jointGenEigenspace (componentRightTranslation j) (χ ω i))
    (hU : ∀ ω i, i ∈ s → (U i ↔ χ ω i ∈ unitaryExponents A))
    (hk : ∀ ω i, i ∈ s →
      ((componentRightTranslation j a - χ ω i a • 1) ^ k i) (c ω i) = 0)
    (hr : ∀ i ∈ s, ¬ U i → r i < 1)
    (hbound : ∀ ω i, i ∈ s → ¬ U i → ‖χ ω i a‖₊ ≤ r i) :
    HasUniformSplitAnnihilators j a (fun ω => ∑ i ∈ s, c ω i) := by
  classical
  let sw := s.filter U
  let sp := s.filter (fun i => ¬ U i)
  have hθ : (sp.sup r) < 1 := by
    rw [Finset.sup_lt_iff (by norm_num)]
    intro i hi
    obtain ⟨his, hiU⟩ := Finset.mem_filter.mp hi
    exact hr i his hiU
  have hann : ∀ ω (t : Finset ι), t ⊆ s →
      aeval (GroupAction.rightFunctions (j a))
        (∏ i ∈ t, (X - C (χ ω i a)) ^ k i) (∑ i ∈ t, c ω i) = 0 := by
    intro ω t ht
    refine aeval_prod_apply_sum_eq_zero _ _ _ _ fun i hi => ?_
    rw [map_pow, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]
    exact hk ω i (ht hi)
  refine ⟨∑ i ∈ sw, k i, ∑ i ∈ sp, k i, (sp.sup r : NNReal),
    (fun ω => ∏ i ∈ sw, (X - C (χ ω i a)) ^ k i),
    (fun ω => ∏ i ∈ sp, (X - C (χ ω i a)) ^ k i),
    NNReal.coe_nonneg _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast hθ
  · intro ω
    exact monic_prod_of_monic _ _ fun i _ => (monic_X_sub_C _).pow _
  · intro ω
    exact monic_prod_of_monic _ _ fun i _ => (monic_X_sub_C _).pow _
  · intro ω
    rw [natDegree_prod_of_monic _ _ (fun i _ => (monic_X_sub_C _).pow _)]
    simp only [natDegree_pow, natDegree_X_sub_C, mul_one]
  · intro ω
    rw [natDegree_prod_of_monic _ _ (fun i _ => (monic_X_sub_C _).pow _)]
    simp only [natDegree_pow, natDegree_X_sub_C, mul_one]
  · intro ω z hz
    obtain ⟨i, hi, rfl⟩ := exists_eq_of_mem_roots_prod hz
    obtain ⟨his, hiU⟩ := Finset.mem_filter.mp hi
    exact ((hU ω i his).mp hiU) a
  · intro ω z hz
    obtain ⟨i, hi, rfl⟩ := exists_eq_of_mem_roots_prod hz
    obtain ⟨his, hiU⟩ := Finset.mem_filter.mp hi
    have h := (hbound ω i his hiU).trans (Finset.le_sup (f := r) hi)
    exact_mod_cast h
  · intro ω
    rw [weakPart_sum_labels j s (χ ω) (c ω) (hc ω) U (hU ω)]
    exact hann ω sw (Finset.filter_subset _ _)
  · intro ω
    rw [positivePart_sum_labels j s (χ ω) (c ω) (hc ω) U (hU ω)]
    exact hann ω sp (Finset.filter_subset _ _)

end Langlands.HarishChandraSchwartz

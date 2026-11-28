import Langlands.Global.AdelicSymmetricFamilyGram
import Langlands.Analysis.Meromorphic.ScalarIdentity

/-! # Finite weighted expansions for the intertwining families of wave packets -/

noncomputable section

set_option autoImplicit false

open Set

namespace Langlands.Global

open Langlands.Analysis.Meromorphic

/-- Finite entire-weighted sums of meromorphic expansions have expansions of a common
length on one domain. The allowed vectors may depend on the family index. -/
def WavePacketWeightedExpansionsStatement : Prop :=
  ∀ {I X Y : Type*} [Fintype I] [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X]
    {q : ℕ} (Z : Set X) (Pr : I → (Y → ℂ) → Prop) (reg : ℝ → X → Prop)
    (b : I → Fin q → X → ℂ) (Mv : I → Fin q → X → Y → ℂ),
    (∀ i, Pr i 0) →
    (∀ ⦃R R' : ℝ⦄, R ≤ R' → ∀ ⦃x⦄, reg R' x → reg R x) →
    (∀ i l, IsMeromorphicInCoordinatesOn (b i l) univ) →
    (∀ i l, ∃ (k : ℕ) (ψ : Fin k → Y → ℂ) (coeff : Fin k → X → ℂ) (D : Set X),
      (∀ a, Pr i (ψ a)) ∧ Z ⊆ D ∧ (∀ a, IsMeromorphicInCoordinatesOn (coeff a) D) ∧
      ∃ R : ℝ, ∀ x, reg R x → ∀ g, Mv i l x g = ∑ a, coeff a x * ψ a g) →
    ∃ (m : ℕ) (ψ : I → Fin m → Y → ℂ) (coeff : I → Fin m → X → ℂ) (D : Set X),
      (∀ i a, Pr i (ψ i a)) ∧ Z ⊆ D ∧ (∀ i a, IsMeromorphicInCoordinatesOn (coeff i a) D) ∧
      ∀ i, ∃ R : ℝ, ∀ x, reg R x → ∀ g,
        ∑ l, b i l x * Mv i l x g = ∑ a, coeff i a x * ψ i a g

/-- Intersect the domains, pad each original expansion and distribute the entire weights. -/
theorem wavePacketWeightedExpansions : WavePacketWeightedExpansionsStatement := by
  classical
  intro I X Y _ _ _ _ q Z Pr reg b Mv hzero hreg hb hMv
  have h (p : I × Fin q) := hMv p.1 p.2
  choose k ψ coeff D hψ hZD hcoeff R hR using h
  choose O hDO hO hcoeffO using fun p => exists_openDense_domain (hcoeff p)
  let m : ℕ := Finset.univ.sup k
  have hkm (p : I × Fin q) : k p ≤ m := Finset.le_sup (Finset.mem_univ p)
  let U := ⋂ p, O p
  have hU : IsOpenDenseInCoordinates U := isOpenDenseInCoordinates_iInter_of_finite hO
  have hZU : Z ⊆ U := fun x hx => mem_iInter.mpr fun p => hDO p (hZD p hx)
  let ψpad (p : I × Fin q) (a : Fin m) : Y → ℂ :=
    if ha : (a : ℕ) < k p then ψ p ⟨a, ha⟩ else 0
  let cpad (p : I × Fin q) (a : Fin m) : X → ℂ :=
    if ha : (a : ℕ) < k p then coeff p ⟨a, ha⟩ else 0
  have hp (p : I × Fin q) (a : Fin m) : Pr p.1 (ψpad p a) := by
    by_cases ha : (a : ℕ) < k p
    · simpa only [ψpad, ha, ↓reduceDIte] using hψ p ⟨a, ha⟩
    · simpa only [ψpad, ha, ↓reduceDIte] using hzero p.1
  have hc (p : I × Fin q) (a : Fin m) : IsMeromorphicInCoordinatesOn (cpad p a) U := by
    by_cases ha : (a : ℕ) < k p
    · simp only [cpad, ha, ↓reduceDIte]
      exact (hcoeffO p ⟨a, ha⟩).congr_mono hU (iInter_subset _ p) (fun _ _ => rfl)
    · simp only [cpad, ha, ↓reduceDIte]
      exact (isMeromorphicInCoordinatesOn_const (0 : ℂ)).congr_mono hU (subset_univ _) (fun _ _ => rfl)
  let e : Fin q × Fin m ≃ Fin (q * m) := finProdFinEquiv
  refine ⟨q * m, fun i a => ψpad (i, (e.symm a).1) (e.symm a).2,
    fun i a x => b i (e.symm a).1 x * cpad (i, (e.symm a).1) (e.symm a).2 x, U,
    fun i a => hp (i, (e.symm a).1) (e.symm a).2, hZU, ?_, ?_⟩
  · intro i a
    exact ((hb i (e.symm a).1).mul (hc (i, (e.symm a).1) (e.symm a).2)).congr_mono
      hU (fun _ hx => ⟨mem_univ _, hx⟩) (fun _ _ => rfl)
  · intro i
    let thresholds : Fin q → ℝ := fun l => R (i, l)
    obtain ⟨R₀, hR₀⟩ := (Set.finite_range thresholds).bddAbove
    refine ⟨R₀, fun x hx g => ?_⟩
    rw [← e.sum_comp]
    simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hR (i, l) x (hreg (hR₀ (mem_range_self l)) hx) g, ← sum_fin_pad (hkm (i, l)),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : (a : ℕ) < k (i, l)
    · simp only [cpad, ψpad, ha, ↓reduceDIte, mul_assoc]
    · simp only [cpad, ψpad, ha, ↓reduceDIte, Pi.zero_apply, mul_zero]

end Langlands.Global

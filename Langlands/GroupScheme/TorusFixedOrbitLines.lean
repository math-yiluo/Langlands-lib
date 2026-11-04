import Langlands.GroupScheme.FlagCoreLinear

/-! # Two fixed lines from a nontrivial torus orbit -/

noncomputable section

open Matrix

namespace Langlands.GroupScheme.FlagCore

variable {k : Type*} [Field k] [Infinite k]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {I : Type*} [Fintype I] {Γ : Type*} [Group Γ]
    {ρ : Γ →* GL ι k} {P : GL ι k} {wt : ι → I → ℤ}
    {τ : (I → kˣ) → Γ} {e : ι → k}

/-- Two actual group representatives whose orbit vectors span distinct
torus-fixed lines. -/
structure TorusFixedOrbitLinePair (ρ : Γ →* GL ι k)
    (τ : (I → kˣ) → Γ) (e : ι → k) where
  first : Γ
  second : Γ
  first_fixed : IsTorusFixed ρ τ (orbitVec ρ e first)
  second_fixed : IsTorusFixed ρ τ (orbitVec ρ e second)
  not_smul : ¬ ∃ a : k, orbitVec ρ e first = a • orbitVec ρ e second

/-- A non-fixed line in a closed projective group orbit has two
nonproportional torus-fixed orbit lines. The torus is given by its actual
simultaneous diagonalization, and fixedness concerns all its parameters. -/
theorem exists_two_torusFixed_orbitLines
    (he : e ≠ 0) (ho : IsClosedOrbit (orbitVec ρ e))
    (hτ : ∀ s, (ρ (τ s) : Matrix ι ι k) =
      (P : Matrix ι ι k) * diagonal (fun i => (charValue wt s i : k)) *
        (↑P⁻¹ : Matrix ι ι k))
    (g : Γ) (hg : ¬ IsTorusFixed ρ τ (orbitVec ρ e g)) :
    ∃ g₁ g₂ : Γ,
      IsTorusFixed ρ τ (orbitVec ρ e g₁) ∧
      IsTorusFixed ρ τ (orbitVec ρ e g₂) ∧
      ¬ ∃ a : k, orbitVec ρ e g₁ = a • orbitVec ρ e g₂ := by
  classical
  obtain ⟨ν, hν⟩ := exists_separating wt
  let d : ι → ℤ := fun i => ∑ a, ν a * wt i a
  let u : ι → k := (↑P⁻¹ : Matrix ι ι k) *ᵥ orbitVec ρ e g
  have hu : (P : Matrix ι ι k) *ᵥ u = orbitVec ρ e g := by
    simp only [u, mulVec_mulVec, Units.mul_inv, one_mulVec]
  have hu0 : u ≠ 0 := mulVec_ne_zero P⁻¹ (orbitVec_ne_zero ρ he g)
  obtain ⟨c, hc, i, hi, hdi⟩ := exists_min_level d u hu0
  obtain ⟨c', hc', j, hj, hdj⟩ := exists_min_level (fun i => -d i) u hu0
  have hsep : ∀ i l, d i = d l → wt i = wt l := hν
  have hsep' : ∀ i l, -d i = -d l → wt i = wt l := by
    intro i l h
    exact hsep i l (by omega)
  have hcc' : c ≠ -c' := by
    intro h
    apply hg
    rw [← hu]
    apply isTorusFixed_of_level hτ hsep u c
    intro l hl
    have h₁ := hc l hl
    have h₂ := hc' l hl
    omega
  obtain ⟨g₁, a, ha, h₁⟩ := exists_orbitVec_weightPart ho hτ
    (ν := ν) (d := d) (fun _ => rfl) g u hu c hc ⟨i, hi, hdi⟩
  have hd' : ∀ i, -d i = ∑ a, (-ν a) * wt i a := by
    intro i
    simp [d, Finset.sum_neg_distrib]
  obtain ⟨g₂, b, hb, h₂⟩ := exists_orbitVec_weightPart ho hτ
    (ν := fun a => -ν a) (d := fun i => -d i) hd' g u hu c' hc' ⟨j, hj, hdj⟩
  refine ⟨g₁, g₂, isTorusFixed_of_eq_smul hτ hsep ha h₁,
    isTorusFixed_of_eq_smul hτ hsep' hb h₂, ?_⟩
  rintro ⟨t, ht⟩
  have hscaled :
      b • ((P : Matrix ι ι k) *ᵥ weightPart d u c) =
        (a * t) • ((P : Matrix ι ι k) *ᵥ weightPart (fun i => -d i) u c') := by
    rw [h₁, h₂, ht, smul_smul, smul_smul, smul_smul]
    congr 1
    ring
  have hparts := congrArg (fun v => (↑P⁻¹ : Matrix ι ι k) *ᵥ v) hscaled
  simp only [mulVec_smul, mulVec_mulVec, Units.inv_mul, one_mulVec] at hparts
  have hnot : -c ≠ c' := by omega
  have hi' := congrFun hparts i
  simp only [Pi.smul_apply, smul_eq_mul, weightPart, GeneralLinear.weightPart,
    hdi, ite_true, hnot, ite_false, mul_zero] at hi'
  exact mul_ne_zero hb hi hi'

/-- Choose the two actual representatives supplied by the extreme-weight
contractions, together with their fixedness and nonproportionality proofs. -/
noncomputable def twoTorusFixedOrbitLines
    (he : e ≠ 0) (ho : IsClosedOrbit (orbitVec ρ e))
    (hτ : ∀ s, (ρ (τ s) : Matrix ι ι k) =
      (P : Matrix ι ι k) * diagonal (fun i => (charValue wt s i : k)) *
        (↑P⁻¹ : Matrix ι ι k))
    (g : Γ) (hg : ¬ IsTorusFixed ρ τ (orbitVec ρ e g)) :
    TorusFixedOrbitLinePair ρ τ e := by
  classical
  apply Classical.choice
  obtain ⟨g₁, g₂, h₁, h₂, hne⟩ :=
    exists_two_torusFixed_orbitLines he ho hτ g hg
  exact ⟨⟨g₁, g₂, h₁, h₂, hne⟩⟩

end Langlands.GroupScheme.FlagCore

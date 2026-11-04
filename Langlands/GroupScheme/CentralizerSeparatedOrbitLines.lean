import Langlands.GroupScheme.FlagCoreLinear

/-! # Extreme orbit lines separated under the torus centralizer -/

noncomputable section

open Matrix

namespace Langlands.GroupScheme.FlagCore

variable {k : Type*} [Field k] [Infinite k]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {I : Type*} [Fintype I] {Γ : Type*} [Group Γ]
    {ρ : Γ →* GL ι k} {P : GL ι k} {wt : ι → I → ℤ}
    {τ : (I → kˣ) → Γ} {e : ι → k}

/-- Two torus-fixed orbit lines that cannot be related by a torus-centralizing
point and a scalar. -/
structure CentralizerSeparatedOrbitLinePair (ρ : Γ →* GL ι k)
    (τ : (I → kˣ) → Γ) (e : ι → k) where
  first : Γ
  second : Γ
  first_fixed : IsTorusFixed ρ τ (orbitVec ρ e first)
  second_fixed : IsTorusFixed ρ τ (orbitVec ρ e second)
  separated : ∀ x : Γ, (∀ s, Commute x (τ s)) →
    ¬ ∃ a : k, orbitVec ρ e first = a •
      ((ρ x : Matrix ι ι k) *ᵥ orbitVec ρ e second)

omit [Infinite k] in
private theorem cochar_eigen_of_level
    (hτ : ∀ s, (ρ (τ s) : Matrix ι ι k) =
      (P : Matrix ι ι k) * diagonal (fun i => (charValue wt s i : k)) *
        (↑P⁻¹ : Matrix ι ι k))
    {ν : I → ℤ} {d : ι → ℤ} (hd : ∀ i, d i = ∑ a, ν a * wt i a)
    (u : ι → k) (c : ℤ) (hu : ∀ i, u i ≠ 0 → d i = c) (z : kˣ) :
    (ρ (τ (fun a => z ^ ν a)) : Matrix ι ι k) *ᵥ ((P : Matrix ι ι k) *ᵥ u) =
      ((z ^ c : kˣ) : k) • ((P : Matrix ι ι k) *ᵥ u) := by
  rw [hτ, conj_mulVec]
  have heq : diagonal (fun i => (charValue wt (fun a => z ^ ν a) i : k)) *ᵥ u =
      ((z ^ c : kˣ) : k) • u := by
    funext i
    rw [mulVec_diagonal]
    by_cases hi : u i = 0
    · simp [hi]
    · simp only [charValue_cochar wt hd, hu i hi, Pi.smul_apply, smul_eq_mul]
  rw [heq, mulVec_smul]

/-- Nonfixedness supplies two extreme orbit lines with different cocharacter
weights; a torus-centralizing point preserves these weights. -/
theorem exists_centralizerSeparated_orbitLines
    (he : e ≠ 0) (ho : IsClosedOrbit (orbitVec ρ e))
    (hτ : ∀ s, (ρ (τ s) : Matrix ι ι k) =
      (P : Matrix ι ι k) * diagonal (fun i => (charValue wt s i : k)) *
        (↑P⁻¹ : Matrix ι ι k))
    (g : Γ) (hg : ¬ IsTorusFixed ρ τ (orbitVec ρ e g)) :
    ∃ g₁ g₂ : Γ,
      IsTorusFixed ρ τ (orbitVec ρ e g₁) ∧
      IsTorusFixed ρ τ (orbitVec ρ e g₂) ∧
      ∀ x : Γ, (∀ s, Commute x (τ s)) →
        ¬ ∃ a : k, orbitVec ρ e g₁ = a •
          ((ρ x : Matrix ι ι k) *ᵥ orbitVec ρ e g₂) := by
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
  have heig₁ : ∀ z : kˣ,
      (ρ (τ (fun a => z ^ ν a)) : Matrix ι ι k) *ᵥ orbitVec ρ e g₁ =
        ((z ^ c : kˣ) : k) • orbitVec ρ e g₁ := by
    intro z
    apply smul_right_injective (ι → k) ha
    have h := cochar_eigen_of_level hτ (ν := ν) (d := d) (fun _ => rfl)
      (weightPart d u c) c (fun _ h => weightPart_ne_zero_level h) z
    rw [h₁, mulVec_smul, smul_comm ((z ^ c : kˣ) : k) a] at h
    exact h
  have heig₂ : ∀ z : kˣ,
      (ρ (τ (fun a => z ^ ν a)) : Matrix ι ι k) *ᵥ orbitVec ρ e g₂ =
        ((z ^ (-c') : kˣ) : k) • orbitVec ρ e g₂ := by
    intro z
    apply smul_right_injective (ι → k) hb
    have h := cochar_eigen_of_level hτ (ν := ν) (d := d) (fun _ => rfl)
      (weightPart (fun i => -d i) u c') (-c')
      (fun i h => by have := weightPart_ne_zero_level h; omega) z
    rw [h₂, mulVec_smul, smul_comm ((z ^ (-c') : kˣ) : k) b] at h
    exact h
  refine ⟨g₁, g₂, isTorusFixed_of_eq_smul hτ hsep ha h₁,
    isTorusFixed_of_eq_smul hτ hsep' hb h₂, ?_⟩
  intro x hx
  rintro ⟨t, ht⟩
  apply hcc'
  apply eq_of_forall_zpow_eq (k := k)
  intro z
  apply Units.ext
  have hmat : (ρ (τ (fun a => z ^ ν a)) : Matrix ι ι k) * (ρ x : Matrix ι ι k) =
      (ρ x : Matrix ι ι k) * (ρ (τ (fun a => z ^ ν a)) : Matrix ι ι k) := by
    exact congrArg Units.val ((hx (fun a => z ^ ν a)).symm.map ρ).eq
  have heig : (ρ (τ (fun a => z ^ ν a)) : Matrix ι ι k) *ᵥ orbitVec ρ e g₁ =
      ((z ^ (-c') : kˣ) : k) • orbitVec ρ e g₁ := by
    rw [ht, mulVec_smul, mulVec_mulVec, hmat, ← mulVec_mulVec, heig₂,
      mulVec_smul, smul_comm]
  exact smul_left_injective k (orbitVec_ne_zero ρ he g₁) ((heig₁ z).symm.trans heig)

/-- Choose the two actual extreme orbit representatives, keeping their
separation under every point centralizing the torus parameters. -/
def centralizerSeparatedOrbitLines
    (he : e ≠ 0) (ho : IsClosedOrbit (orbitVec ρ e))
    (hτ : ∀ s, (ρ (τ s) : Matrix ι ι k) =
      (P : Matrix ι ι k) * diagonal (fun i => (charValue wt s i : k)) *
        (↑P⁻¹ : Matrix ι ι k))
    (g : Γ) (hg : ¬ IsTorusFixed ρ τ (orbitVec ρ e g)) :
    CentralizerSeparatedOrbitLinePair ρ τ e := by
  apply Classical.choice
  obtain ⟨g₁, g₂, h₁, h₂, hsep⟩ := exists_centralizerSeparated_orbitLines he ho hτ g hg
  exact ⟨⟨g₁, g₂, h₁, h₂, hsep⟩⟩

end Langlands.GroupScheme.FlagCore

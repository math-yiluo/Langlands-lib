import Langlands.Analysis.FundamentalDomainFibreAverage

/-! # Comparing fundamental domains of two lattices with a common Levi part

Let `Λ = M · j(Γ)` and `Λ' = M · j(Γ')` be countable subgroups of `H` with the same factor `M`,
where `Γ, Γ' ≤ V` and `j : V → H`. For a function invariant under `Λ` and `j(V)`, the integrals
over strict fundamental domains of `Λ` and `Λ'` are proportional, with ratio `ν(C') / ν(C)` for
fundamental domains `C`, `C'` of `Γ`, `Γ'` in `V`. In the adelic application `Λ' = aΛa⁻¹` for a
point `a` of a split component, and the ratio is the modulus of `a` on the unipotent radical. -/

noncomputable section

open MeasureTheory Set Function
open scoped ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Langlands.Analysis.LatticeComparison

local notation "𝟙[" D "]" => Set.indicator D (fun _ => (1 : ℝ≥0∞))

variable {H : Type*} [Group H] [MeasurableSpace H] [MeasurableMul₂ H] [MeasurableInv H]
  {V : Type*} [Group V] [MeasurableSpace V] [MeasurableMul₂ V] [MeasurableInv V]

/-- Unfolding: for a strict fundamental domain `D` of `Λ` and a left `Λ`-invariant `φ`,
`∫_{D'} φ = ∫_D φ · N` with `N g = Σ_λ 1_{D'}(λ g)`. -/
theorem setLIntegral_eq_setLIntegral_mul_count (μ : Measure H) [μ.IsMulLeftInvariant]
    (Λ : Subgroup H) [Countable Λ] {D D' : Set H} (hDm : MeasurableSet D)
    (hD'm : MeasurableSet D') (hD : ∀ x : H, ∃! l : Λ, (l : H) * x ∈ D)
    {φ : H → ℝ≥0∞} (hφ : Measurable φ) (hφΛ : ∀ l : Λ, ∀ x, φ (l * x) = φ x) :
    ∫⁻ g in D', φ g ∂μ = ∫⁻ g in D, φ g * ∑' l : Λ, 𝟙[D'] ((l : H) * g) ∂μ := by
  have hDfd : IsFundamentalDomain Λ D μ := IsFundamentalDomain.mk' hDm.nullMeasurableSet hD
  calc ∫⁻ g in D', φ g ∂μ = ∫⁻ h, 𝟙[D'] h * φ h ∂μ := by
        rw [← lintegral_indicator hD'm]
        refine lintegral_congr fun h => ?_
        by_cases hh : h ∈ D' <;> simp [hh]
    _ = ∑' l : Λ, ∫⁻ g in D, 𝟙[D'] (l • g) * φ (l • g) ∂μ := hDfd.lintegral_eq_tsum'' _
    _ = ∑' l : Λ, ∫⁻ g in D, φ g * 𝟙[D'] ((l : H) * g) ∂μ := by
        refine tsum_congr fun l => setLIntegral_congr_fun hDm fun g _ => ?_
        simp only [Subgroup.smul_def, smul_eq_mul, hφΛ]
        exact mul_comm _ _
    _ = ∫⁻ g in D, ∑' l : Λ, φ g * 𝟙[D'] ((l : H) * g) ∂μ := by
        refine (lintegral_tsum fun l => ?_).symm
        exact (hφ.mul ((measurable_const.indicator hD'm).comp
          (measurable_const.mul measurable_id))).aemeasurable
    _ = _ := by simp_rw [ENNReal.tsum_mul_left]

/-- Orbit sum over a lattice `Λ = M · j(Γ)`: summing over `Λ` and integrating over a fundamental
domain `C` of `Γ` is summing over `M` and integrating over all of `V`. -/
theorem tsum_setLIntegral_eq_tsum_lintegral (ν : Measure V) [ν.IsMulLeftInvariant]
    (Λ : Subgroup H) (j : V →* H) (Γ : Subgroup V) [Countable Γ]
    {C : Set V} (hC : IsFundamentalDomain Γ C ν) {M : Type*} (m : M → H)
    (e : M × Γ ≃ Λ) (he : ∀ p, (e p : H) = m p.1 * j p.2) (D' : Set H) (g : H) :
    ∑' l : Λ, ∫⁻ v in C, 𝟙[D'] ((l : H) * (j v * g)) ∂ν =
      ∑' x : M, ∫⁻ v, 𝟙[D'] (m x * (j v * g)) ∂ν := by
  rw [← e.tsum_eq, ENNReal.tsum_prod']
  refine tsum_congr fun x => ?_
  rw [hC.lintegral_eq_tsum'' (fun v => 𝟙[D'] (m x * (j v * g)))]
  refine tsum_congr fun c => lintegral_congr fun v => ?_
  rw [he]
  simp only [Subgroup.smul_def, smul_eq_mul, map_mul, mul_assoc]

/-- **Comparison of two lattices with a common Levi part.** Let `Λ = M · j(Γ)` and
`Λ' = M · j(Γ')` (unique factorizations) have strict fundamental domains `D` and `D'`, and let
`C`, `C'` be fundamental domains of `Γ`, `Γ'` in `V`. If `Λ` normalizes `j(V)` through
`ν`-preserving conjugations stabilizing `Γ`, then for every measurable `φ ≥ 0` invariant under
`Λ` and under `j(V)` on the left, `ν(C) ∫_{D'} φ = ν(C') ∫_D φ`. -/
theorem mul_setLIntegral_eq (μ : Measure H) [μ.IsMulLeftInvariant] [SFinite μ]
    (Λ Λ' : Subgroup H) [Countable Λ] [Countable Λ'] {D D' : Set H}
    (hDm : MeasurableSet D) (hD'm : MeasurableSet D')
    (hD : ∀ x : H, ∃! l : Λ, (l : H) * x ∈ D) (hD' : ∀ x : H, ∃! l : Λ', (l : H) * x ∈ D')
    (j : V →* H) (hj : Measurable j) (hjinj : Injective j)
    (Γ Γ' : Subgroup V) [Countable Γ] [Countable Γ'] (hΓ : ∀ v ∈ Γ, j v ∈ Λ)
    (cj : Λ → V → V) (hcj : ∀ l v, j (cj l v) = l * j v * (l : H)⁻¹)
    (hΓc : ∀ (l : Λ) (v : V), v ∈ Γ → cj l v ∈ Γ)
    (ν : Measure V) [ν.IsMulLeftInvariant] [ν.IsInvInvariant] [SFinite ν]
    (hcjm : ∀ l, MeasurePreserving (cj l) ν ν)
    {C C' : Set V} (hCm : MeasurableSet C) (hC : IsFundamentalDomain Γ C ν)
    (hC' : IsFundamentalDomain Γ' C' ν)
    {M : Type*} (m : M → H) (e : M × Γ ≃ Λ) (he : ∀ p, (e p : H) = m p.1 * j p.2)
    (e' : M × Γ' ≃ Λ') (he' : ∀ p, (e' p : H) = m p.1 * j p.2)
    {φ : H → ℝ≥0∞} (hφ : Measurable φ) (hφΛ : ∀ l : Λ, ∀ x, φ (l * x) = φ x)
    (hφV : ∀ v x, φ (j v * x) = φ x) :
    ν C * ∫⁻ g in D', φ g ∂μ = ν C' * ∫⁻ g in D, φ g ∂μ := by
  set N : H → ℝ≥0∞ := fun g => ∑' l : Λ, 𝟙[D'] ((l : H) * g) with hNdef
  have hind : ∀ (L : Subgroup H) (l : L), Measurable fun x : H => 𝟙[D'] ((l : H) * x) :=
    fun L l => (measurable_const.indicator hD'm).comp (measurable_const.mul measurable_id)
  have hN : Measurable N := Measurable.tsum fun l => hind Λ l
  have hNΛ : ∀ l : Λ, ∀ x, N (l * x) = N x := by
    intro l x
    show ∑' l' : Λ, 𝟙[D'] ((l' : H) * (l * x)) = ∑' l' : Λ, 𝟙[D'] ((l' : H) * x)
    rw [← (Equiv.mulRight l).tsum_eq (fun l'' : Λ => 𝟙[D'] ((l'' : H) * x))]
    refine tsum_congr fun l' => ?_
    simp [mul_assoc]
  have h1 := setLIntegral_eq_setLIntegral_mul_count μ Λ hDm hD'm hD hφ hφΛ
  have hfib := FibreAverage.setLIntegral_fibreAverage μ Λ D hDm hD j hj hjinj Γ hΓ cj hcj hΓc ν
    hcjm C hCm hC (F := fun g => φ g * N g) (hφ.mul hN) (fun l x => by rw [hφΛ, hNΛ])
  have hcount : ∀ g, ∫⁻ v in C, N (j v * g) ∂ν = ν C' := by
    intro g
    have hv : ∀ (L : Subgroup H) (l : L), Measurable fun v : V => 𝟙[D'] ((l : H) * (j v * g)) :=
      fun L l => (hind L l).comp (hj.mul_const g)
    simp only [hNdef]
    rw [lintegral_tsum fun l => (hv Λ l).aemeasurable,
      tsum_setLIntegral_eq_tsum_lintegral ν Λ j Γ hC m e he D' g,
      ← tsum_setLIntegral_eq_tsum_lintegral ν Λ' j Γ' hC' m e' he' D' g,
      ← lintegral_tsum fun l => (hv Λ' l).aemeasurable]
    simp_rw [FibreAverage.tsum_indicator_mul_eq_one Λ' hD']
    rw [setLIntegral_const, one_mul]
  calc ν C * ∫⁻ g in D', φ g ∂μ = ν C * ∫⁻ g in D, φ g * N g ∂μ := by rw [h1]
    _ = ∫⁻ g in D, ∫⁻ v in C, φ (j v * g) * N (j v * g) ∂ν ∂μ := hfib.symm
    _ = ∫⁻ g in D, φ g * ν C' ∂μ := by
        refine lintegral_congr fun g => ?_
        simp_rw [hφV]
        rw [lintegral_const_mul (φ g) (f := fun v => N (j v * g)) (hN.comp (hj.mul_const g)),
          hcount]
    _ = ν C' * ∫⁻ g in D, φ g ∂μ := by rw [lintegral_mul_const _ hφ, mul_comm]

universe u v w

/-- **Statement form.** Two countable subgroups `Λ = M · j(Γ)` and `Λ' = M · j(Γ')` of a group
`H` with a common factor `M` and unique factorizations, with strict fundamental domains `D`, `D'`
for a left-invariant s-finite measure `μ`; `Λ` normalizes `j(V)` through `ν`-preserving
conjugations that stabilize `Γ`; `C`, `C'` measurable fundamental domains of `Γ`, `Γ'` in `V` for a
left- and inversion-invariant s-finite `ν`. Then `ν(C) ∫_{D'} φ = ν(C') ∫_D φ` for every
measurable `φ ≥ 0` that is left invariant under `Λ` and under `j(V)`. -/
def LatticeComparisonStatement : Prop :=
  ∀ {H : Type u} [Group H] [MeasurableSpace H] [MeasurableMul₂ H] [MeasurableInv H]
    {V : Type v} [Group V] [MeasurableSpace V] [MeasurableMul₂ V] [MeasurableInv V]
    (μ : Measure H) [μ.IsMulLeftInvariant] [SFinite μ]
    (Λ Λ' : Subgroup H) [Countable Λ] [Countable Λ'] {D D' : Set H},
    MeasurableSet D → MeasurableSet D' →
    (∀ x : H, ∃! l : Λ, (l : H) * x ∈ D) → (∀ x : H, ∃! l : Λ', (l : H) * x ∈ D') →
    ∀ (j : V →* H), Measurable j → Injective j →
    ∀ (Γ Γ' : Subgroup V) [Countable Γ] [Countable Γ'], (∀ v ∈ Γ, j v ∈ Λ) →
    ∀ (cj : Λ → V → V), (∀ l v, j (cj l v) = l * j v * (l : H)⁻¹) →
    (∀ (l : Λ) (v : V), v ∈ Γ → cj l v ∈ Γ) →
    ∀ (ν : Measure V) [ν.IsMulLeftInvariant] [ν.IsInvInvariant] [SFinite ν],
    (∀ l, MeasurePreserving (cj l) ν ν) →
    ∀ {C C' : Set V}, MeasurableSet C → IsFundamentalDomain Γ C ν → IsFundamentalDomain Γ' C' ν →
    ∀ {M : Type w} (m : M → H) (e : M × Γ ≃ Λ), (∀ p, (e p : H) = m p.1 * j p.2) →
    ∀ (e' : M × Γ' ≃ Λ'), (∀ p, (e' p : H) = m p.1 * j p.2) →
    ∀ {φ : H → ℝ≥0∞}, Measurable φ → (∀ l : Λ, ∀ x, φ (l * x) = φ x) →
      (∀ v x, φ (j v * x) = φ x) →
      ν C * ∫⁻ g in D', φ g ∂μ = ν C' * ∫⁻ g in D, φ g ∂μ

/-- Proof of `LatticeComparisonStatement`. -/
theorem latticeComparison : LatticeComparisonStatement.{u, v, w} := by
  intro H _ _ _ _ V _ _ _ _ μ _ _ Λ Λ' _ _ D D' hDm hD'm hD hD' j hj hjinj Γ Γ' _ _ hΓ cj hcj hΓc
    ν _ _ _ hcjm C C' hCm hC hC' M m e he e' he' φ hφ hφΛ hφV
  exact mul_setLIntegral_eq μ Λ Λ' hDm hD'm hD hD' j hj hjinj Γ Γ' hΓ cj hcj hΓc ν hcjm hCm hC hC'
    m e he e' he' hφ hφΛ hφV

end Langlands.Analysis.LatticeComparison

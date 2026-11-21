import Langlands.Analysis.FundamentalDomainConstantTermL2

/-! # Invariance of the folded constant term

The folded constant term `foldConstantTerm` of any function is left-invariant under `Λ` and, when
`ν` is also right invariant, under `j(V)`, at every point. -/

noncomputable section

open MeasureTheory Set Function
open scoped ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Langlands.Analysis.FibreAverage

variable {H : Type*} [Group H] [MeasurableSpace H] [MeasurableMul₂ H] [MeasurableInv H]
  {V : Type*} [Group V] [MeasurableSpace V] [MeasurableMul₂ V] [MeasurableInv V]
  (Λ : Subgroup H) [Countable Λ] (D : Set H)
  (hD : ∀ x : H, ∃! l : Λ, (l : H) * x ∈ D)
  (j : V →* H) (hjinj : Injective j)
  (Γ : Subgroup V) (hΓ : ∀ v ∈ Γ, j v ∈ Λ)
  (cj : Λ → V → V) (hcj : ∀ l v, j (cj l v) = l * j v * (l : H)⁻¹)
  (hΓc : ∀ (l : Λ) (v : V), v ∈ Γ → cj l v ∈ Γ)
  (ν : Measure V) [ν.IsMulLeftInvariant]
  (hcjm : ∀ l, MeasurePreserving (cj l) ν ν)
  (C : Set V) (hC : IsFundamentalDomain Γ C ν)

include hjinj hcj in
theorem cj_inv_cj' (l : Λ) (v : V) : cj l⁻¹ (cj l v) = v := by
  apply hjinj
  rw [hcj, hcj]
  simp [mul_assoc]

include hjinj hcj in
theorem cj_mul' (l : Λ) (v w : V) : cj l (v * w) = cj l v * cj l w := by
  apply hjinj
  rw [map_mul, hcj, hcj, hcj, map_mul]
  group

include hjinj hcj hΓc hcjm hC in
/-- The preimage of `C` under `cj l` is again a fundamental domain of `Γ`. -/
theorem isFundamentalDomain_preimage_cj' (l : Λ) : IsFundamentalDomain Γ (cj l ⁻¹' C) ν := by
  have hh : ∀ v, cj l (cj l⁻¹ v) = v := fun v => by
    have := cj_inv_cj' Λ j hjinj cj hcj l⁻¹ v
    rwa [inv_inv] at this
  let e : Γ → Γ := fun γ => ⟨cj l⁻¹ γ, hΓc l⁻¹ γ γ.2⟩
  have he : Bijective e := by
    refine ⟨fun γ γ' h => ?_, fun γ => ?_⟩
    · apply Subtype.ext
      have := congrArg (fun x : Γ => cj l (x : V)) h
      simp only [e] at this
      rwa [hh, hh] at this
    · refine ⟨⟨cj l γ, hΓc l γ γ.2⟩, Subtype.ext ?_⟩
      exact cj_inv_cj' Λ j hjinj cj hcj l (γ : V)
  refine hC.preimage_of_equiv (hcjm l).quasiMeasurePreserving he fun γ x => ?_
  change cj l (cj l⁻¹ γ * x) = (γ : V) * cj l x
  rw [cj_mul' Λ j hjinj cj hcj, hh]

include hjinj hcj hΓ hΓc hcjm hC in
/-- **`Λ`-invariance of the folded constant term**, at every point. -/
theorem foldConstantTerm_mul_left [Countable Γ] (l : Λ) (f : H → ℂ) (g : H) :
    foldConstantTerm Λ D hD j ν C f ((l : H) * g) = foldConstantTerm Λ D hD j ν C f g := by
  unfold foldConstantTerm
  congr 1
  let ψ : V → ℂ := fun v => f (fold Λ hD (j v * g))
  have hh : ∀ v, cj l (cj l⁻¹ v) = v := fun v => by
    have := cj_inv_cj' Λ j hjinj cj hcj l⁻¹ v
    rwa [inv_inv] at this
  have h1 : ∀ v, f (fold Λ hD (j v * ((l : H) * g))) = ψ (cj l⁻¹ v) := fun v => by
    have hmul : j v * ((l : H) * g) = (l : H) * (j (cj l⁻¹ v) * g) := by
      rw [hcj]
      simp only [InvMemClass.coe_inv, inv_inv]
      group
    simp only [ψ, hmul, fold_mul_left]
  simp_rw [h1]
  let e : V ≃ᵐ V :=
    { toFun := cj l⁻¹
      invFun := cj l
      left_inv := hh
      right_inv := fun v => cj_inv_cj' Λ j hjinj cj hcj l v
      measurable_toFun := (hcjm l⁻¹).measurable
      measurable_invFun := (hcjm l).measurable }
  have hpre : C = cj l⁻¹ ⁻¹' (cj l ⁻¹' C) := by
    ext v
    simp [hh]
  have hψΓ : ∀ (c : Γ) (v : V), ψ (c • v) = ψ v := fun c v => by
    simp only [ψ, Subgroup.smul_def, smul_eq_mul, map_mul, mul_assoc]
    exact congrArg f (fold_mul_left Λ hD ⟨j c, hΓ c c.2⟩ _)
  calc ∫ v in C, ψ (cj l⁻¹ v) ∂ν = ∫ v in cj l⁻¹ ⁻¹' (cj l ⁻¹' C), ψ (cj l⁻¹ v) ∂ν := by
        rw [← hpre]
    _ = ∫ v in cj l ⁻¹' C, ψ v ∂ν :=
        (hcjm l⁻¹).setIntegral_preimage_emb e.measurableEmbedding ψ _
    _ = ∫ v in C, ψ v ∂ν :=
        (isFundamentalDomain_preimage_cj' Λ j hjinj Γ cj hcj hΓc ν hcjm C hC l).setIntegral_eq hC hψΓ

include hΓ hC in
/-- **`j(V)`-invariance of the folded constant term**, at every point, when `ν` is also right
invariant. -/
theorem foldConstantTerm_mul_left_j [Countable Γ] [ν.IsMulRightInvariant] (w : V) (f : H → ℂ)
    (g : H) :
    foldConstantTerm Λ D hD j ν C f (j w * g) = foldConstantTerm Λ D hD j ν C f g := by
  unfold foldConstantTerm
  congr 1
  let ψ : V → ℂ := fun v => f (fold Λ hD (j v * g))
  have h1 : ∀ v, f (fold Λ hD (j v * (j w * g))) = ψ (v * w) := fun v => by
    simp only [ψ, map_mul, mul_assoc]
  simp_rw [h1]
  have hψΓ : ∀ (c : Γ) (v : V), ψ (c • v) = ψ v := fun c v => by
    simp only [ψ, Subgroup.smul_def, smul_eq_mul, map_mul, mul_assoc]
    exact congrArg f (fold_mul_left Λ hD ⟨j c, hΓ c c.2⟩ _)
  have hpre : C = (fun v => v * w) ⁻¹' ((fun v => v * w⁻¹) ⁻¹' C) := by
    ext v
    simp
  have hCw : IsFundamentalDomain Γ ((fun v => v * w⁻¹) ⁻¹' C) ν := by
    refine hC.preimage_of_equiv (measurePreserving_mul_right ν w⁻¹).quasiMeasurePreserving
      (Equiv.refl Γ).bijective fun c v => ?_
    change (c : V) * v * w⁻¹ = (c : V) * (v * w⁻¹)
    rw [mul_assoc]
  calc ∫ v in C, ψ (v * w) ∂ν = ∫ v in (fun v => v * w) ⁻¹' ((fun v => v * w⁻¹) ⁻¹' C),
        ψ (v * w) ∂ν := by rw [← hpre]
    _ = ∫ v in (fun v => v * w⁻¹) ⁻¹' C, ψ v ∂ν :=
        (measurePreserving_mul_right ν w).setIntegral_preimage_emb
          (measurableEmbedding_mulRight w) ψ _
    _ = ∫ v in C, ψ v ∂ν := hCw.setIntegral_eq hC hψΓ

universe u v

/-- **Statement form.** In the setting of the folded constant term (`foldConstantTerm`), with `Γ`
countable and `ν` left and right invariant, the folded constant term of every function is, at every
point, left-invariant under `Λ` and under `j(V)`. -/
def FoldConstantTermInvarianceStatement : Prop :=
  ∀ {H : Type u} [Group H] [MeasurableSpace H] [MeasurableMul₂ H] [MeasurableInv H]
    {V : Type v} [Group V] [MeasurableSpace V] [MeasurableMul₂ V] [MeasurableInv V]
    (Λ : Subgroup H) [Countable Λ] (D : Set H) (hD : ∀ x : H, ∃! l : Λ, (l : H) * x ∈ D)
    (j : V →* H), Injective j →
    ∀ (Γ : Subgroup V) [Countable Γ], (∀ v ∈ Γ, j v ∈ Λ) →
    ∀ (cj : Λ → V → V), (∀ l v, j (cj l v) = l * j v * (l : H)⁻¹) →
    (∀ (l : Λ) (v : V), v ∈ Γ → cj l v ∈ Γ) →
    ∀ (ν : Measure V) [ν.IsMulLeftInvariant] [ν.IsMulRightInvariant],
    (∀ l, MeasurePreserving (cj l) ν ν) →
    ∀ (C : Set V), IsFundamentalDomain Γ C ν → ∀ (f : H → ℂ) (g : H),
      (∀ l : Λ, foldConstantTerm Λ D hD j ν C f ((l : H) * g) = foldConstantTerm Λ D hD j ν C f g) ∧
      (∀ w : V, foldConstantTerm Λ D hD j ν C f (j w * g) = foldConstantTerm Λ D hD j ν C f g)

/-- Proof of `FoldConstantTermInvarianceStatement`. -/
theorem foldConstantTermInvariance : FoldConstantTermInvarianceStatement.{u, v} := by
  intro H _ _ _ _ V _ _ _ _ Λ _ D hD j hjinj Γ _ hΓ cj hcj hΓc ν _ _ hcjm C hC f g
  exact ⟨fun l => foldConstantTerm_mul_left Λ D hD j hjinj Γ hΓ cj hcj hΓc ν hcjm C hC l f g,
    fun w => foldConstantTerm_mul_left_j Λ D hD j Γ hΓ ν C hC w f g⟩

end Langlands.Analysis.FibreAverage

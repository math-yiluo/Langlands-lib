import Langlands.Analysis.FundamentalDomainLatticeComparison

/-! # Left translation by an element centralizing the Levi part of a lattice

If `Λ = M · j(Γ)` and `a` commutes with `M` and normalizes `j(V)`, then `aΛa⁻¹ = M · j(aΓa⁻¹)` and
`aD` is a strict fundamental domain of `aΛa⁻¹`. The lattice comparison theorem then gives, for
measurable `φ ≥ 0` invariant under `Λ` and `j(V)`, the cross-multiplied identity
`ν(C) · ∫_D φ(a g) dμ(g) = ν(aCa⁻¹) · ∫_D φ dμ`. It is a ratio formula only when
`0 < ν(C) < ∞`, which is not assumed. Here the whole integrand `φ` is translated; no weight is held
fixed. -/

noncomputable section

open MeasureTheory Set Function
open scoped ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Langlands.Analysis.LatticeComparison

variable {H : Type*} [Group H] [MeasurableSpace H] [MeasurableMul₂ H] [MeasurableInv H]
  {V : Type*} [Group V] [MeasurableSpace V] [MeasurableMul₂ V] [MeasurableInv V]

/-- **Translation by a centralizing element.** Let `Λ = M · j(Γ)` with unique factorizations,
`a ∈ H` commuting with `M` and normalizing `j(V)` through an automorphism `α` of `V` whose inverse
is quasi-measure-preserving. For every measurable `φ ≥ 0` left invariant under `Λ` and `j(V)`,
`ν(C) ∫_D φ(a g) dg = ν(α(C)) ∫_D φ`. -/
theorem mul_setLIntegral_mul_left_eq (μ : Measure H) [μ.IsMulLeftInvariant] [SFinite μ]
    (Λ : Subgroup H) [Countable Λ] {D : Set H} (hDm : MeasurableSet D)
    (hD : ∀ x : H, ∃! l : Λ, (l : H) * x ∈ D)
    (j : V →* H) (hj : Measurable j) (hjinj : Injective j)
    (Γ : Subgroup V) [Countable Γ] (hΓ : ∀ v ∈ Γ, j v ∈ Λ)
    (cj : Λ → V → V) (hcj : ∀ l v, j (cj l v) = l * j v * (l : H)⁻¹)
    (hΓc : ∀ (l : Λ) (v : V), v ∈ Γ → cj l v ∈ Γ)
    (ν : Measure V) [ν.IsMulLeftInvariant] [ν.IsInvInvariant] [SFinite ν]
    (hcjm : ∀ l, MeasurePreserving (cj l) ν ν)
    {C : Set V} (hCm : MeasurableSet C) (hC : IsFundamentalDomain Γ C ν)
    {M : Type*} (m : M → H) (e : M × Γ ≃ Λ) (he : ∀ p, (e p : H) = m p.1 * j p.2)
    (a : H) (hm : ∀ x, a * m x = m x * a) (α : V ≃* V) (hαj : ∀ v, j (α v) = a * j v * a⁻¹)
    (hα : Measure.QuasiMeasurePreserving α.symm ν ν)
    {φ : H → ℝ≥0∞} (hφ : Measurable φ) (hφΛ : ∀ l : Λ, ∀ x, φ (l * x) = φ x)
    (hφV : ∀ v x, φ (j v * x) = φ x) :
    ν C * ∫⁻ g in D, φ (a * g) ∂μ = ν (α.symm ⁻¹' C) * ∫⁻ g in D, φ g ∂μ := by
  -- the conjugate lattice and its data
  let κ : H →* H := (MulAut.conj a).toMonoidHom
  have hκ : Injective κ := (MulAut.conj a).injective
  let Λ' := Λ.map κ
  let eΛ : Λ ≃* Λ' := Λ.equivMapOfInjective κ hκ
  have heΛ : ∀ l : Λ, ((eΛ l : Λ') : H) = a * l * a⁻¹ := fun l => rfl
  let Γ' := Γ.map α.toMonoidHom
  let eΓ : Γ ≃* Γ' := Γ.equivMapOfInjective α.toMonoidHom α.injective
  have heΓ : ∀ γ : Γ, ((eΓ γ : Γ') : V) = α γ := fun γ => rfl
  have : Countable Λ' := Countable.of_equiv _ eΛ.toEquiv
  have : Countable Γ' := Countable.of_equiv _ eΓ.toEquiv
  let D' : Set H := (fun y => a⁻¹ * y) ⁻¹' D
  have hD'm : MeasurableSet D' := hDm.preimage (measurable_const_mul a⁻¹)
  have hD' : ∀ x : H, ∃! l : Λ', (l : H) * x ∈ D' := by
    intro x
    obtain ⟨l, hl, huniq⟩ := hD (a⁻¹ * x)
    refine ⟨eΛ l, ?_, fun l' hl' => ?_⟩
    · change a⁻¹ * ((eΛ l : H) * x) ∈ D
      rw [heΛ]
      simpa [mul_assoc] using hl
    · have h1 : eΛ.symm l' = l := by
        apply huniq
        have h2 : ((eΛ (eΛ.symm l') : Λ') : H) = l' := by rw [MulEquiv.apply_symm_apply]
        rw [heΛ] at h2
        change a⁻¹ * ((l' : H) * x) ∈ D at hl'
        rw [← h2] at hl'
        simpa [mul_assoc] using hl'
      rw [← h1, MulEquiv.apply_symm_apply]
  let C' : Set V := α.symm ⁻¹' C
  have hC' : IsFundamentalDomain Γ' C' ν :=
    hC.preimage_of_equiv hα eΓ.bijective fun γ v => by
      change α.symm ((eΓ γ : V) * v) = (γ : V) * α.symm v
      rw [heΓ, map_mul, MulEquiv.symm_apply_apply]
  let e' : M × Γ' ≃ Λ' :=
    ((Equiv.prodCongr (Equiv.refl M) eΓ.toEquiv).symm.trans e).trans eΛ.toEquiv
  have he' : ∀ p, (e' p : H) = m p.1 * j p.2 := by
    rintro ⟨x, γ'⟩
    change ((eΛ (e (x, eΓ.symm γ')) : Λ') : H) = m x * j γ'
    rw [heΛ, he]
    have hγ : α ((eΓ.symm γ' : Γ) : V) = γ' := by
      rw [← heΓ, MulEquiv.apply_symm_apply]
    calc a * (m x * j ((eΓ.symm γ' : Γ) : V)) * a⁻¹
        = (a * m x * a⁻¹) * (a * j ((eΓ.symm γ' : Γ) : V) * a⁻¹) := by group
      _ = m x * j γ' := by rw [hm, ← hαj, hγ]; group
  have key := mul_setLIntegral_eq μ Λ Λ' hDm hD'm hD hD' j hj hjinj Γ Γ' hΓ cj hcj hΓc ν hcjm
    hCm hC hC' m e he e' he' hφ hφΛ hφV
  have htrans : ∫⁻ g in D', φ g ∂μ = ∫⁻ g in D, φ (a * g) ∂μ := by
    have h := (measurePreserving_mul_left μ a).setLIntegral_comp_preimage_emb
      (measurableEmbedding_mulLeft a) φ D'
    have hpre : (fun g => a * g) ⁻¹' D' = D := by
      ext g
      simp [D']
    rw [hpre] at h
    exact h.symm
  rw [← htrans]
  exact key

universe u v w

/-- **Statement form** of `mul_setLIntegral_mul_left_eq`. -/
def ConjugateTranslationStatement : Prop :=
  ∀ {H : Type u} [Group H] [MeasurableSpace H] [MeasurableMul₂ H] [MeasurableInv H]
    {V : Type v} [Group V] [MeasurableSpace V] [MeasurableMul₂ V] [MeasurableInv V]
    (μ : Measure H) [μ.IsMulLeftInvariant] [SFinite μ]
    (Λ : Subgroup H) [Countable Λ] {D : Set H}, MeasurableSet D →
    (∀ x : H, ∃! l : Λ, (l : H) * x ∈ D) →
    ∀ (j : V →* H), Measurable j → Injective j →
    ∀ (Γ : Subgroup V) [Countable Γ], (∀ v ∈ Γ, j v ∈ Λ) →
    ∀ (cj : Λ → V → V), (∀ l v, j (cj l v) = l * j v * (l : H)⁻¹) →
    (∀ (l : Λ) (v : V), v ∈ Γ → cj l v ∈ Γ) →
    ∀ (ν : Measure V) [ν.IsMulLeftInvariant] [ν.IsInvInvariant] [SFinite ν],
    (∀ l, MeasurePreserving (cj l) ν ν) →
    ∀ {C : Set V}, MeasurableSet C → IsFundamentalDomain Γ C ν →
    ∀ {M : Type w} (m : M → H) (e : M × Γ ≃ Λ), (∀ p, (e p : H) = m p.1 * j p.2) →
    ∀ (a : H), (∀ x, a * m x = m x * a) →
    ∀ (α : V ≃* V), (∀ v, j (α v) = a * j v * a⁻¹) → Measure.QuasiMeasurePreserving α.symm ν ν →
    ∀ {φ : H → ℝ≥0∞}, Measurable φ → (∀ l : Λ, ∀ x, φ (l * x) = φ x) →
      (∀ v x, φ (j v * x) = φ x) →
      ν C * ∫⁻ g in D, φ (a * g) ∂μ = ν (α.symm ⁻¹' C) * ∫⁻ g in D, φ g ∂μ

/-- Proof of `ConjugateTranslationStatement`. -/
theorem conjugateTranslation : ConjugateTranslationStatement.{u, v, w} := by
  intro H _ _ _ _ V _ _ _ _ μ _ _ Λ _ D hDm hD j hj hjinj Γ _ hΓ cj hcj hΓc ν _ _ _ hcjm C hCm hC
    M m e he a hm α hαj hα φ hφ hφΛ hφV
  exact mul_setLIntegral_mul_left_eq μ Λ hDm hD j hj hjinj Γ hΓ cj hcj hΓc ν hcjm hCm hC m e he
    a hm α hαj hα hφ hφΛ hφV

end Langlands.Analysis.LatticeComparison

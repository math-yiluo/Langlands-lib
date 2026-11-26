import Langlands.BaseChange.TwistedVanDijk.KernelFormula

/-! # The diagonal of the kernel is the twisted constant term

The sum `∑_x c k(x, x)` over the cosets of a level, with `c` the mass of the level, is the
twisted constant term `φ^{P,σ}` composed with the action of `σ` on the Levi. See the paired
Markdown.
-/

noncomputable section

namespace Langlands.BaseChange.TwistedVanDijk

open MeasureTheory Measure GeneralLinear HarmonicAnalysis
open scoped ENNReal NNReal

universe u v

variable {F : Type u} [Field F] [TopologicalSpace F]
  {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [IsModuleTopology F E] (σ : E ≃ₐ[F] E) {n : ℕ} (B : BlockShape n)

attribute [local instance] LocalFieldTopology.t2Space
  LocalFieldTopology.generalLinear_t2Space
  LocalFieldTopology.generalLinear_locallyCompactSpace
  LocalFieldTopology.generalLinear_secondCountableTopology
  unipotentSubgroup_secondCountable unipotentSubgroup_locallyCompact
  parabolic_secondCountable parabolic_locallyCompact integralGL_compactSpace
  integralGL_secondCountable

variable [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]
  (μU : Measure (B.unipotentSubgroup E)) [μU.IsHaarMeasure]
  (μK : Measure (integralGL E n)) [μK.IsHaarMeasure] [IsProbabilityMeasure μK]

/-- The diagonal kernel values sum to the twisted constant term at `σ(m)`. -/
theorem sum_kernelValue_diag {φ : SchwartzBruhat (GeneralLinear n E)} (L : Level σ ⇑φ)
    (m : B.Levi E) :
    ∑ x : L.Cosets, (μK.real (L.inner : Set (integralGL E n)) : ℂ) *
        kernelValue σ B μU φ (L.rep x) (L.rep x) m =
      ((LocalFieldData.ofInstances E).leviHalfModulus B (leviAut σ B m) : ℂ) *
        ∫ y, ∫ κ, φ ((κ : GeneralLinear n E)⁻¹ * B.leviEmbedding E (leviAut σ B m) *
          (y : GeneralLinear n E) * entrywiseAut σ n κ) ∂μK ∂μU := by
  -- The finite sum is the integral over `K`.
  have hsum : (∑ x : L.Cosets, (μK.real (L.inner : Set (integralGL E n)) : ℂ) *
        kernelValue σ B μU φ (L.rep x) (L.rep x) m) =
      ∫ k : integralGL E n, kernelValue σ B μU φ k k m ∂μK := by
    refine (integral_eq_sum_quotient_out μK L.inner
      ((L.K'.isOpen.preimage continuous_subtype_val).measurableSet)
      (fun k : integralGL E n => kernelValue σ B μU φ k k m) ?_).symm
    intro h h' hh'
    have hk : ((h' : integralGL E n) : GeneralLinear n E) ∈ L.K' := hh'
    simp only [Subgroup.coe_mul]
    rw [kernelValue_mul_right_left σ B μU L.left _ _ hk,
      kernelValue_mul_right_right σ B μU (fun k hk x => L.right x k hk) L.sigma_mem _ _ hk]
  rw [hsum]
  simp only [kernelValue]
  rw [integral_const_mul]
  have hδ : ((LocalFieldData.ofInstances E).leviHalfModulus B (leviAut σ B m) : ℂ) =
      ((LocalFieldData.ofInstances E).leviHalfModulus B m : ℂ) := by
    rw [LocalFieldData.leviHalfModulus_apply, LocalFieldData.leviHalfModulus_apply,
      leviModulus_leviAut]
  rw [hδ]
  congr 1
  -- Fubini: integrate over `U` first.
  let f : integralGL E n → B.unipotentSubgroup E → ℂ := fun k u =>
    φ ((k : GeneralLinear n E)⁻¹ * entrywiseAut σ n
      (B.leviEmbedding E m * (u : GeneralLinear n E) * k))
  have hfc : Continuous (Function.uncurry f) := by
    refine φ.continuous.comp ?_
    exact ((continuous_subtype_val.comp continuous_fst).inv).mul
      ((continuous_entrywiseAut σ n).comp ((continuous_const.mul
        (continuous_subtype_val.comp continuous_snd)).mul (continuous_subtype_val.comp
          continuous_fst)))
  -- Compact support in `u`.
  let C : Set (GeneralLinear n E) := (fun p : GeneralLinear n E × GeneralLinear n E =>
    (B.leviEmbedding E m)⁻¹ * entrywiseAut σ.symm n (p.1 * p.2) * p.1⁻¹ ) ''
      ((integralGL E n : Set (GeneralLinear n E)) ×ˢ tsupport φ)
  have hC : IsCompact C := ((isCompact_integralGL n).prod φ.hasCompactSupport).image
    ((continuous_const.mul ((continuous_entrywiseAut_symm σ n).comp
      (continuous_fst.mul continuous_snd))).mul continuous_fst.inv)
  have hUC : IsCompact {u : B.unipotentSubgroup E | (u : GeneralLinear n E) ∈ C} :=
    (B.isClosed_unipotentSubgroup E).isClosedEmbedding_subtypeVal.isCompact_preimage hC
  have hint : Integrable (Function.uncurry f) (μK.prod μU) := by
    refine hfc.integrable_of_hasCompactSupport
      (HasCompactSupport.intro (isCompact_univ.prod hUC) fun p hp => ?_)
    by_contra hne
    apply hp
    refine ⟨Set.mem_univ _, ?_⟩
    refine ⟨((p.1 : GeneralLinear n E), (p.1 : GeneralLinear n E)⁻¹ * entrywiseAut σ n
      (B.leviEmbedding E m * (p.2 : GeneralLinear n E) * p.1)), ⟨p.1.property,
        subset_tsupport φ hne⟩, ?_⟩
    simp only [mul_inv_cancel_left]
    change (B.leviEmbedding E m)⁻¹ * (entrywiseAut σ n).symm (entrywiseAut σ n
      (B.leviEmbedding E m * (p.2 : GeneralLinear n E) * p.1)) * (p.1 : GeneralLinear n E)⁻¹ =
      (p.2 : GeneralLinear n E)
    rw [MulEquiv.symm_apply_apply]
    group
  change (∫ k, ∫ u, f k u ∂μU ∂μK) = _
  rw [integral_integral_swap hint]
  -- The substitution `u ↦ σ(u)` in `U`.
  let F' : B.unipotentSubgroup E → ℂ := fun y => ∫ κ, φ ((κ : GeneralLinear n E)⁻¹ *
    B.leviEmbedding E (leviAut σ B m) * (y : GeneralLinear n E) * entrywiseAut σ n κ) ∂μK
  have hF' : ∀ u : B.unipotentSubgroup E,
      (∫ k, f k u ∂μK) = F' (unipotentContinuousAut σ B u) := by
    intro u
    simp only [f, F']
    congr 1
    funext k
    rw [coe_unipotentContinuousAut, ← entrywiseAut_leviEmbedding, map_mul, map_mul, mul_assoc,
      mul_assoc, mul_assoc]
  simp_rw [hF']
  have hmeas : MeasurableEmbedding (unipotentContinuousAut σ B) :=
    (unipotentContinuousAut σ B).toHomeomorph.isClosedEmbedding.measurableEmbedding
  rw [← hmeas.integral_map, map_unipotentAut_eq σ B μU]

end Langlands.BaseChange.TwistedVanDijk

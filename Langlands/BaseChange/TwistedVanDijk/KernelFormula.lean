import Langlands.BaseChange.TwistedVanDijk.Operator

/-! # The kernel formula for the induced twisted operator

For a test function `φ` with a level `K'` and a `K'`-fixed vector `ξ` of the normalized product
induction, the value at `g` of `π(φ) ι(A) ξ` is the finite sum
`∑_x c (A₁ ⊗ ⋯ ⊗ A_r) τ(k(g, x)) ξ(x)` over the cosets of `K'` in `GL_n(𝒪_E)`, with `c` the
mass of `K'`. See the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange.TwistedVanDijk

open MeasureTheory Measure GeneralLinear HarmonicAnalysis
open scoped ENNReal NNReal

universe u v uW

section Compactness

variable {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E] {n : ℕ} (B : BlockShape n)

attribute [local instance] LocalFieldTopology.t2Space
  LocalFieldTopology.generalLinear_t2Space
  LocalFieldTopology.generalLinear_locallyCompactSpace
  LocalFieldTopology.generalLinear_secondCountableTopology
  unipotentSubgroup_secondCountable unipotentSubgroup_locallyCompact
  parabolic_secondCountable parabolic_locallyCompact integralGL_compactSpace
  integralGL_secondCountable

/-- The points `(m, u)` with `m u k ∈ C` for some `k ∈ GL_n(𝒪_E)` lie in a compact set. -/
theorem exists_isCompact_iwasawa_preimage {C : Set (GeneralLinear n E)} (hC : IsCompact C) :
    ∃ S : Set (B.Levi E × B.unipotentSubgroup E), IsCompact S ∧
      ∀ (x : B.Levi E × B.unipotentSubgroup E) (k : integralGL E n),
        B.leviEmbedding E x.1 * (x.2 : GeneralLinear n E) * (k : GeneralLinear n E) ∈ C →
          x ∈ S := by
  let D : Set (GeneralLinear n E) := (fun p : GeneralLinear n E × GeneralLinear n E =>
    p.1 * p.2⁻¹) '' (C ×ˢ (integralGL E n : Set (GeneralLinear n E)))
  have hD : IsCompact D := (hC.prod (isCompact_integralGL n)).image
    (continuous_fst.mul continuous_snd.inv)
  have hPD : IsCompact {p : B.parabolic E | (p : GeneralLinear n E) ∈ D} :=
    (B.isClosed_parabolic E).isClosedEmbedding_subtypeVal.isCompact_preimage hD
  refine ⟨parabolicProductHomeomorph (R := E) B ⁻¹'
    {p : B.parabolic E | (p : GeneralLinear n E) ∈ D},
    (parabolicProductHomeomorph (R := E) B).isCompact_preimage.mpr hPD, ?_⟩
  intro x k hx
  refine ⟨(B.leviEmbedding E x.1 * (x.2 : GeneralLinear n E) * (k : GeneralLinear n E), k),
    ⟨hx, k.property⟩, ?_⟩
  simp

end Compactness

section Formula

variable {F : Type u} [Field F] [TopologicalSpace F]
  {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [IsModuleTopology F E] (σ : E ≃ₐ[F] E) {n : ℕ} (B : BlockShape n)
  {W : Fin B.length → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
  {P : ∀ i, Representation ℂ (GeneralLinear (B.size i) E) (W i)}
  (hP : ∀ i, IsAdmissible (P i)) (A : ∀ i, SigmaIntertwiner σ (B.size i) (P i))

/-- Evaluation at `g` of a smooth induced function, as a linear map. -/
def evalLinear (g : GeneralLinear n E) :
    Induction.SmoothFunctions (B.parabolic E)
        (twist ((LocalFieldData.ofInstances E).parabolicHalfModulus B)
          ((B.blockTensor P).comp (B.leviProjection E))) →ₗ[ℂ] PiTensorProduct ℂ W where
  toFun f := Induction.eval _ _ f g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

attribute [local instance] LocalFieldTopology.t2Space
  LocalFieldTopology.generalLinear_t2Space
  LocalFieldTopology.generalLinear_locallyCompactSpace
  LocalFieldTopology.generalLinear_secondCountableTopology
  unipotentSubgroup_secondCountable unipotentSubgroup_locallyCompact
  parabolic_secondCountable parabolic_locallyCompact integralGL_compactSpace
  integralGL_secondCountable

variable [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]
  [MeasurableSpace (B.Levi E)] [BorelSpace (B.Levi E)]
  (μG : Measure (GeneralLinear n E)) [μG.IsHaarMeasure]
  (μM : Measure (B.Levi E)) [μM.IsHaarMeasure]
  (μU : Measure (B.unipotentSubgroup E)) [μU.IsHaarMeasure]
  (μK : Measure (integralGL E n)) [μK.IsHaarMeasure] [IsProbabilityMeasure μK]

omit [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]
  [MeasurableSpace (B.Levi E)] [BorelSpace (B.Levi E)] in
/-- Evaluations of a smooth induced function are locally constant. -/
theorem isLocallyConstant_eval
    (ξ : Induction.SmoothFunctions (B.parabolic E)
        (twist ((LocalFieldData.ofInstances E).parabolicHalfModulus B)
          ((B.blockTensor P).comp (B.leviProjection E)))) :
    IsLocallyConstant (Induction.eval _ _ ξ) := by
  obtain ⟨K₀, hK₀⟩ := Induction.exists_openSubgroup_eval_mul (B.parabolic E) _ ξ
  exact Induction.isLocallyConstant_of_mul_right K₀.toSubgroup K₀.isOpen _
    (fun x k hk => hK₀ ⟨k, hk⟩ x)

/-- The kernel formula: `(π(φ) ι(A) ξ)(g) = ∑_x c (A₁ ⊗ ⋯ ⊗ A_r) τ(k(g, x)) ξ(x)` for `ξ`
fixed by the level. -/
theorem eval_integratedAction_inducedSigmaIntertwiner
    (hG : μG (integralGL E n) = 1)
    (hM : μM {x | ∀ i, x i ∈ integralGL E (B.size i)} = 1)
    (hU : μU {y | (y : GeneralLinear n E) ∈ integralGL E n} = 1)
    {φ : SchwartzBruhat (GeneralLinear n E)} (L : Level σ ⇑φ)
    (ξ : Induction.SmoothFunctions (B.parabolic E)
        (twist ((LocalFieldData.ofInstances E).parabolicHalfModulus B)
          ((B.blockTensor P).comp (B.leviProjection E))))
    (hξ : ξ ∈ fixedVectors ((LocalFieldData.ofInstances E).normalizedProductInduced B P)
      (L.K' : Subgroup (GeneralLinear n E)))
    (g : GeneralLinear n E) :
    Induction.eval _ _ (Hecke.integratedAction μG
        ((LocalFieldData.ofInstances E).normalizedProductInduced B P)
        (isAdmissible_normalizedProductInduced B P hP).1 φ
        ((inducedSigmaIntertwiner σ B A).toLinearMap ξ)) g =
      compactSum σ B μU μM hP A μK L (fun x => Induction.eval _ _ ξ (L.rep x)) g := by
  apply Module.eval_apply_injective ℂ
  apply LinearMap.ext
  intro Λ
  let ℓ : PiTensorProduct ℂ W →ₗ[ℂ] ℂ := Λ ∘ₗ (leviTensorIntertwiner σ B A).toLinearMap
  let ev : _ → PiTensorProduct ℂ W := Induction.eval (B.parabolic E)
    (twist ((LocalFieldData.ofInstances E).parabolicHalfModulus B)
      ((B.blockTensor P).comp (B.leviProjection E))) ξ
  change Λ (evalLinear B g _) = Λ (compactSum σ B μU μM hP A μK L _ g)
  -- Step 1: the integrated action against the functional `Λ ∘ eval_g`.
  have h1 : Λ (evalLinear B g (Hecke.integratedAction μG
        ((LocalFieldData.ofInstances E).normalizedProductInduced B P)
        (isAdmissible_normalizedProductInduced B P hP).1 φ
        ((inducedSigmaIntertwiner σ B A).toLinearMap ξ))) =
      ∫ h, φ h * ℓ (ev (entrywiseAut σ.symm n (g * h))) ∂μG :=
    Hecke.integratedAction_dual μG _ _ φ _ (Λ ∘ₗ evalLinear B g)
  -- Step 2: the change of variables `h = g⁻¹ σ(h')`.
  let θ : GeneralLinear n E ≃ₜ GeneralLinear n E :=
    (entrywiseContinuousAut σ n).toHomeomorph.trans (Homeomorph.mulLeft g⁻¹)
  have hθ : ∀ h, θ h = g⁻¹ * entrywiseAut σ n h := fun h => rfl
  have hθμ : μG.map θ = μG := by
    have hcomp : ⇑θ = (fun x => g⁻¹ * x) ∘ (entrywiseContinuousAut σ n) := rfl
    rw [hcomp, ← Measure.map_map (measurable_const_mul _)
      (map_continuous (entrywiseContinuousAut σ n)).measurable,
      map_entrywiseAut_eq σ μG, map_mul_left_eq_self]
  let H : GeneralLinear n E → ℂ := fun h => φ (θ h) * ℓ (ev h)
  have hHc : Continuous H :=
    (φ.continuous.comp θ.continuous).mul ((isLocallyConstant_eval B ξ).comp ℓ).continuous
  have h2 : (∫ h, φ h * ℓ (ev (entrywiseAut σ.symm n (g * h))) ∂μG) = ∫ h, H h ∂μG := by
    conv_lhs => rw [← hθμ]
    rw [θ.isClosedEmbedding.measurableEmbedding.integral_map]
    congr 1
    funext h
    simp only [H, hθ, mul_inv_cancel_left]
    congr 3
    exact (entrywiseAut σ n).symm_apply_apply h
  -- Step 3: the Iwasawa decomposition `dg = dm du dk`.
  let F₃ : (B.Levi E × B.unipotentSubgroup E) × integralGL E n → GeneralLinear n E :=
    fun x => B.leviEmbedding E x.1.1 * (x.1.2 : GeneralLinear n E) * (x.2 : GeneralLinear n E)
  have hF₃c : Continuous F₃ :=
    (((B.leviEmbeddingContinuous E).continuous.comp (continuous_fst.comp continuous_fst)).mul
      (continuous_subtype_val.comp (continuous_snd.comp continuous_fst))).mul
      (continuous_subtype_val.comp continuous_snd)
  have h3 : ∫ h, H h ∂μG = ∫ x, H (F₃ x) ∂((μM.prod μU).prod μK) := by
    conv_lhs => rw [iwasawa_measure_eq B μG μM μU μK hG hM hU]
    exact integral_map hF₃c.measurable.aemeasurable hHc.aestronglyMeasurable
  -- Compact support of the integrand.
  obtain ⟨S, hS, hSx⟩ := exists_isCompact_iwasawa_preimage B
    (θ.isCompact_preimage.mpr φ.hasCompactSupport)
  have hzero : ∀ x : (B.Levi E × B.unipotentSubgroup E) × integralGL E n,
      x.1 ∉ S → H (F₃ x) = 0 := by
    intro x hx
    have hnot : F₃ x ∉ θ ⁻¹' tsupport φ := fun h => hx (hSx x.1 x.2 h)
    simp only [H, image_eq_zero_of_notMem_tsupport hnot, zero_mul]
  have hint : Integrable (fun x => H (F₃ x)) ((μM.prod μU).prod μK) :=
    (hHc.comp hF₃c).integrable_of_hasCompactSupport
      (HasCompactSupport.intro (hS.prod isCompact_univ) fun x hx =>
        hzero x fun h => hx ⟨h, Set.mem_univ _⟩)
  -- Step 4: the covariance of `ξ`.
  have hcov : ∀ x : (B.Levi E × B.unipotentSubgroup E) × integralGL E n,
      H (F₃ x) = φ (θ (F₃ x)) *
        (((LocalFieldData.ofInstances E).leviHalfModulus B x.1.1 : ℂ) *
          ℓ (B.blockTensor P x.1.1 (ev x.2))) := by
    intro x
    have h := (LocalFieldData.ofInstances E).normalizedProductInduced_covariant B P ξ
      (parabolicProduct B x.1) x.2
    rw [leviProjection_parabolicProduct] at h
    simp only [H]
    congr 1
    change ℓ (ev ((parabolicProduct B x.1 : GeneralLinear n E) * x.2)) = _
    refine (congrArg ℓ h).trans ?_
    rw [map_smul, smul_eq_mul, LocalFieldData.leviHalfModulus_apply]
    rfl
  -- Steps 5 and 6: Fubini and the inner integrals.
  have hinner : ∀ k : integralGL E n,
      (∫ y, H (F₃ (y, k)) ∂(μM.prod μU)) =
        ℓ (Hecke.integratedAction μM (B.blockTensor P)
          (FiniteTensor.isAdmissible_external P hP).1
          (kernelTest σ B μU L g (k : GeneralLinear n E)) (ev k)) := by
    intro k
    have hsec : Integrable (fun y => H (F₃ (y, k))) (μM.prod μU) :=
      (hHc.comp (hF₃c.comp (continuous_id.prodMk continuous_const))).integrable_of_hasCompactSupport
        (HasCompactSupport.intro hS fun y hy => hzero (y, k) hy)
    rw [integral_prod _ hsec, Hecke.integratedAction_dual]
    congr 1
    funext m
    simp only [hcov]
    rw [kernelTest_apply, kernelValue, mul_assoc, ← integral_mul_const, ← integral_const_mul]
    congr 1
    funext u
    simp only [hθ, F₃]
    ring
  -- Step 7: the integral over `K` is a finite sum over the cosets of the level.
  have hK : (∫ k : integralGL E n, ℓ (Hecke.integratedAction μM (B.blockTensor P)
        (FiniteTensor.isAdmissible_external P hP).1
        (kernelTest σ B μU L g (k : GeneralLinear n E)) (ev k)) ∂μK) =
      ∑ x : L.Cosets, (μK.real (L.inner : Set (integralGL E n)) : ℂ) *
        ℓ (Hecke.integratedAction μM (B.blockTensor P)
          (FiniteTensor.isAdmissible_external P hP).1
          (kernelTest σ B μU L g (L.rep x)) (ev (L.rep x))) := by
    refine integral_eq_sum_quotient_out μK L.inner
      ((L.K'.isOpen.preimage continuous_subtype_val).measurableSet) _ ?_
    intro h h' hh'
    have hk : ((h' : integralGL E n) : GeneralLinear n E) ∈ L.K' := hh'
    simp only [Subgroup.coe_mul]
    rw [kernelTest_mul_right_right σ B μU L g _ hk]
    have hfix := hξ ⟨_, hk⟩
    have hev : ev ((h : GeneralLinear n E) * ((h' : integralGL E n) : GeneralLinear n E)) =
        ev h :=
      congrArg (fun ζ => Induction.eval _ _ ζ (h : GeneralLinear n E)) hfix
    rw [hev]
  rw [h1, h2, h3, integral_prod_symm _ hint]
  simp_rw [hinner]
  rw [hK]
  simp only [compactSum, _root_.map_sum, map_smul, smul_eq_mul]
  rfl

end Formula

end Langlands.BaseChange.TwistedVanDijk

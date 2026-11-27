import Langlands.Analysis.DistributionFamilyIntegral
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Group.ModularCharacter

/-! # Proportionality of covariant test functionals on a free open orbit -/

noncomputable section

open Function Set MeasureTheory MeasureTheory.Measure TopologicalSpace Topology
open scoped ContDiff Distributions NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Analysis.SmoothOpenOrbit

universe u v w

private theorem continuous_sliceDerivatives
    {Y : Type u} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Y × E → F} (hf : ContDiff ℝ ∞ f) (i : ℕ) :
    Continuous (fun z : Y × E => iteratedFDeriv ℝ i (fun x : E => f (z.1, x)) z.2) := by
  let l := ContinuousLinearMap.inr ℝ Y E
  let L : (Y × E [×i]→L[ℝ] F) →L[ℝ] (E [×i]→L[ℝ] F) :=
    ContinuousMultilinearMap.compContinuousLinearMapL (fun _ => l)
  have hEq (z : Y × E) : iteratedFDeriv ℝ i (fun x : E => f (z.1, x)) z.2 =
      L (iteratedFDeriv ℝ i f z) := by
    let g : Y × E → F := fun y => f ((z.1, 0) + y)
    have hg : ContDiff ℝ ∞ g := hf.comp (contDiff_const.add contDiff_id)
    have he : (fun x : E => f (z.1, x)) = g ∘ l := by
      funext x
      simp [g, l]
    rw [he, l.iteratedFDeriv_comp_right hg _ (by simp),
      show iteratedFDeriv ℝ i g (l z.2) = iteratedFDeriv ℝ i f ((z.1, 0) + l z.2) from
        iteratedFDeriv_comp_add_left i _ _]
    simp [l, L]
  simp only [hEq]
  exact L.continuous.comp (hf.continuous_iteratedFDeriv (m := i) (by simp))

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable (R : H →* Module.End ℝ E)
variable {Ω : Opens E} (e : H ≃ₜ (Ω : Set E)) (x₀ : E)
variable (he : ∀ q : H, (e q).val = R q x₀)

omit [TopologicalSpace H] [IsTopologicalGroup H] [FiniteDimensional ℝ E] in
private theorem action_comp (p q : H) (x : E) : R (p * q) x = R p (R q x) := by
  rw [map_mul, Module.End.mul_apply]

omit [IsTopologicalGroup H] [FiniteDimensional ℝ E] in
include he in
private theorem base_mem : x₀ ∈ Ω := by
  change x₀ ∈ (Ω : Set E)
  simpa only [he, map_one, Module.End.one_apply] using (e 1).property

omit [FiniteDimensional ℝ E] in
include he in
private theorem exists_compact_transporter {K L : Set E} (hK : IsCompact K) (hL : IsCompact L)
    (hKΩ : K ⊆ Ω) (hLΩ : L ⊆ Ω) :
    ∃ S : Set H, IsCompact S ∧ ∀ p x, x ∈ K → R p x ∈ L → p ∈ S := by
  let U : Set E := Ω
  have hpre {C : Set E} (hc : IsCompact C) (hC : C ⊆ Ω) :
      IsCompact (Subtype.val ⁻¹' C : Set U) :=
    IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hc (by simpa using hC)
  let A : Set H := e.symm '' (Subtype.val ⁻¹' K : Set U)
  let B : Set H := e.symm '' (Subtype.val ⁻¹' L : Set U)
  let S := (fun z : H × H => z.2 * z.1⁻¹) '' (A ×ˢ B)
  refine ⟨S, (((hpre hK hKΩ).image e.symm.continuous).prod
    ((hpre hL hLΩ).image e.symm.continuous)).image
      (continuous_snd.mul continuous_fst.inv), ?_⟩
  intro p x hx hy
  let x' : U := ⟨x, hKΩ hx⟩
  let y' : U := ⟨R p x, hLΩ hy⟩
  let a := e.symm x'
  let b := e.symm y'
  have ha : R a x₀ = x := (he a).symm.trans (congrArg Subtype.val (e.apply_symm_apply x'))
  have h : e (p * a) = e b := by
    apply Subtype.ext
    rw [he, action_comp R, ha]
    exact (congrArg Subtype.val (e.apply_symm_apply y')).symm
  have hp : b * a⁻¹ = p := by rw [← e.injective h, mul_inv_cancel_right]
  exact ⟨(a, b), ⟨⟨x', hx, rfl⟩, ⟨y', hy, rfl⟩⟩, hp⟩

include he in
private theorem smooth_weighted_pullbacks
    (hR : Continuous (fun p : H => LinearMap.toContinuousLinearMap (R p)))
    {f g : E → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {K L : Set E} (hK : IsCompact K) (hL : IsCompact L) (hKΩ : K ⊆ Ω) (hLΩ : L ⊆ Ω)
    (hf0 : ∀ x ∉ K, f x = 0) (hg0 : ∀ x ∉ L, g x = 0)
    (j : H ≃ₜ H) {c : H → ℂ} (hc : Continuous c) :
    SmoothCompactFamily (fun p x => c p * (f x * g (R (j p) x))) := by
  let V : (ℂ × (E →L[ℝ] E)) × E → ℂ := fun z => z.1.1 * (f z.2 * g (z.1.2 z.2))
  have hV : ContDiff ℝ ∞ V := by
    dsimp [V]
    fun_prop
  let a : H → ℂ × (E →L[ℝ] E) := fun p => (c p, LinearMap.toContinuousLinearMap (R (j p)))
  have ha : Continuous a := hc.prodMk (hR.comp j.continuous)
  obtain ⟨S, hS, hT⟩ := exists_compact_transporter R e x₀ he hK hL hKΩ hLΩ
  refine ⟨fun p => hV.comp ((contDiff_const (c := a p)).prodMk contDiff_id), fun i => ?_,
    ⟨j ⁻¹' S, j.isCompact_preimage.mpr hS, ?_⟩⟩
  · exact (continuous_sliceDerivatives hV i).comp ((ha.comp continuous_fst).prodMk continuous_snd)
  · intro p hp x
    by_cases hx : x ∈ K
    · rw [hg0 _ (fun hy => hp (hT (j p) x hx hy)), mul_zero, mul_zero]
    · rw [hf0 _ hx, zero_mul, mul_zero]

private def testOfCompact {K : Compacts E} (hK : (K : Set E) ⊆ Ω)
    {f : E → ℂ} (hf : ContDiff ℝ ∞ f) (hf0 : ∀ x ∉ K, f x = 0) : 𝓓(Ω, ℂ) :=
  TestFunction.ofSupportedIn hK (ContDiffMapSupportedIn.of_support_subset hf
    (fun x hx => by by_contra h; exact hx (hf0 x h)))

/-- Covariance for pullback by a linear group action on smooth compact tests. -/
def IsCovariant (χ : H →* ℂ) (T : 𝓓(Ω, ℂ) →L[ℂ] ℂ) : Prop :=
  ∀ (p : H) (f g : 𝓓(Ω, ℂ)), (∀ x, g x = f (R p x)) → T g = χ p * T f

variable [LocallyCompactSpace H] [T2Space H] [SecondCountableTopology H]
  [MeasurableSpace H] [BorelSpace H] (μ : Measure H) [μ.IsHaarMeasure] [μ.InnerRegular]

private def orbitIntegral (χ : H →* ℂ) (f : 𝓓(Ω, ℂ)) (x : E) : ℂ :=
  ∫ p, χ p⁻¹ * f (R p x) ∂μ

omit [FiniteDimensional ℝ E] [T2Space H] [SecondCountableTopology H] in
private theorem orbitIntegral_coordinate (χ : H →* ℂ) (f : 𝓓(Ω, ℂ)) (q : H) :
    orbitIntegral R μ χ f (R q x₀) =
      χ q * ((modularCharacterFun q : ℝ) • orbitIntegral R μ χ f x₀) := by
  let F (p : H) := χ p⁻¹ * f (R p x₀)
  have h (p : H) : χ p⁻¹ * f (R p (R q x₀)) = χ q * F (p * q) := by
    unfold F
    rw [← action_comp R, ← mul_assoc, ← map_mul, mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul]
  simp only [orbitIntegral, h]
  rw [integral_const_mul, ← (measurableEmbedding_mulRight q).integral_map,
    map_right_mul_eq_modularCharacterFun_smul, integral_smul_nnreal_measure]
  rfl

omit [FiniteDimensional ℝ E] [LocallyCompactSpace H] [T2Space H] [SecondCountableTopology H]
  [μ.InnerRegular] in
include he in
private theorem normalization_constant (ρ : E → ℝ) (x : E) (hx : x ∈ Ω) :
    (∫ p, ρ (R p⁻¹ x) ∂μ) = ∫ p, ρ (R p⁻¹ x₀) ∂μ := by
  let q := e.symm ⟨x, hx⟩
  have hq : R q x₀ = x := (he q).symm.trans (congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩))
  rw [← integral_mul_left_eq_self (fun p : H => ρ (R p⁻¹ x)) q]
  apply integral_congr_ae
  refine ae_of_all _ fun p => ?_
  change ρ (R (q * p)⁻¹ x) = ρ (R p⁻¹ x₀)
  rw [← hq, ← action_comp R, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]

omit [LocallyCompactSpace H] [T2Space H] [SecondCountableTopology H] [μ.InnerRegular] in
include he in
private theorem exists_normalized_cutoff
    (hR : Continuous (fun p : H => LinearMap.toContinuousLinearMap (R p))) :
    ∃ (ρ : E → ℝ) (c : ℝ), ContDiff ℝ ∞ ρ ∧ HasCompactSupport ρ ∧ tsupport ρ ⊆ Ω ∧
      0 < c ∧ ∀ x ∈ Ω, (∫ p, ρ (R p⁻¹ x) ∂μ) = c := by
  have hx₀ := base_mem R e x₀ he
  obtain ⟨δ, hδ, hδΩ⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (Ω.isOpen.mem_nhds hx₀)
  let ρ : ContDiffBump x₀ := ⟨δ / 2, δ, by positivity, by linarith⟩
  have hρΩ : tsupport ρ ⊆ Ω := by rw [ρ.tsupport_eq]; exact hδΩ
  have hρ₀ (p : H) : 0 ≤ ρ (R p⁻¹ x₀) := ρ.nonneg
  let c := ∫ p, ρ (R p⁻¹ x₀) ∂μ
  refine ⟨ρ, c, ρ.contDiff, ρ.hasCompactSupport, hρΩ, ?_,
    fun x hx => normalization_constant R e x₀ he μ ρ x hx⟩
  have hc : Continuous (fun p : H => ρ (R p⁻¹ x₀)) :=
    ρ.continuous.comp ((hR.comp continuous_inv).clm_apply continuous_const)
  obtain ⟨S, hS, hT⟩ := exists_compact_transporter R e x₀ he
    (isCompact_singleton (x := x₀)) ρ.hasCompactSupport (singleton_subset_iff.mpr hx₀) hρΩ
  have hcS : HasCompactSupport (fun p : H => ρ (R p⁻¹ x₀)) := by
    apply HasCompactSupport.intro ((Homeomorph.inv H).isCompact_preimage.mpr hS)
    intro p hp
    exact image_eq_zero_of_notMem_tsupport (fun hx => hp (hT p⁻¹ _ (mem_singleton _) hx))
  apply hc.integral_pos_of_hasCompactSupport_nonneg_nonzero hcS hρ₀ (x := 1)
  rw [inv_one, map_one, Module.End.one_apply, ρ.one_of_mem_closedBall (Metric.mem_closedBall_self ρ.rIn_pos.le)]
  exact one_ne_zero

omit [LocallyCompactSpace H] [μ.InnerRegular] in
include he in
private theorem transfer_test_integral
    (hR : Continuous (fun p : H => LinearMap.toContinuousLinearMap (R p)))
    (χ : H →* ℂ) (hχ : Continuous χ) (f : 𝓓(Ω, ℂ))
    {ρ : E → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hρS : HasCompactSupport ρ) (hρΩ : tsupport ρ ⊆ Ω)
    {c : ℝ} (hc : ∀ x ∈ Ω, (∫ p, ρ (R p⁻¹ x) ∂μ) = c) :
    ∃ g : 𝓓(Ω, ℂ), (∀ x, g x = (ρ x : ℂ) * orbitIntegral R μ χ f x) ∧
      ∀ T : 𝓓(Ω, ℂ) →L[ℂ] ℂ, IsCovariant R χ T → T g = (c : ℂ) * T f := by
  let K : Compacts E := ⟨tsupport f, f.hasCompactSupport⟩
  let L : Compacts E := ⟨tsupport ρ, hρS⟩
  let w : E → ℂ := fun x => (ρ x : ℂ)
  have hw : ContDiff ℝ ∞ w := Complex.ofRealCLM.contDiff.comp hρ
  have hf0 (x : E) (hx : x ∉ K) : f x = 0 := image_eq_zero_of_notMem_tsupport hx
  have hw0 (x : E) (hx : x ∉ L) : w x = 0 := by
    change (ρ x : ℂ) = 0
    rw [image_eq_zero_of_notMem_tsupport hx, Complex.ofReal_zero]
  let Φ : H → E → ℂ := fun p x => f x * w (R p⁻¹ x)
  let Ψ : H → E → ℂ := fun p x => χ p⁻¹ * (w x * f (R p x))
  have hΦ : SmoothCompactFamily Φ := by
    have h := smooth_weighted_pullbacks R e x₀ he hR f.contDiff hw K.isCompact L.isCompact
      f.tsupport_subset hρΩ hf0 hw0 (Homeomorph.inv H) (continuous_const (y := (1 : ℂ)))
    change SmoothCompactFamily (fun p x => (1 : ℂ) * (f x * w (R p⁻¹ x))) at h
    simpa only [Φ, one_mul] using h
  have hΨ : SmoothCompactFamily Ψ :=
    smooth_weighted_pullbacks R e x₀ he hR hw f.contDiff L.isCompact K.isCompact
      hρΩ f.tsupport_subset hw0 hf0 (Homeomorph.refl H) (hχ.comp continuous_inv)
  have hΦ0 (p : H) (x : E) (hx : x ∉ K) : Φ p x = 0 := by
    change f x * w (R p⁻¹ x) = 0
    rw [hf0 x hx, zero_mul]
  have hΨ0 (p : H) (x : E) (hx : x ∉ L) : Ψ p x = 0 := by
    change χ p⁻¹ * (w x * f (R p x)) = 0
    rw [hw0 x hx, zero_mul, mul_zero]
  let φ (p : H) : 𝓓(Ω, ℂ) := testOfCompact (K := K) f.tsupport_subset (hΦ.contDiff p) (hΦ0 p)
  let ψ (p : H) : 𝓓(Ω, ℂ) := testOfCompact (K := L) hρΩ (hΨ.contDiff p) (hΨ0 p)
  let g : 𝓓(Ω, ℂ) := testOfCompact (K := L) hρΩ (contDiff_integral_family (μ := μ) hΨ)
    (fun x hx => by simp only [hΨ0 _ x hx, integral_zero])
  have hAvgΦ (x : E) : ((c : ℂ) • f) x = ∫ p, Φ p x ∂μ := by
    change (c : ℂ) * f x = ∫ p, f x * (ρ (R p⁻¹ x) : ℂ) ∂μ
    rw [integral_const_mul, integral_complex_ofReal]
    by_cases hx : x ∈ Ω
    · rw [hc x hx, mul_comm]
    · have hfz : f x = 0 := f.zero_on_compl hx
      rw [hfz, zero_mul, mul_zero]
  refine ⟨g, fun x => ?_, fun T hT => ?_⟩
  · change (∫ p, χ p⁻¹ * (w x * f (R p x)) ∂μ) = w x * ∫ p, χ p⁻¹ * f (R p x) ∂μ
    rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun _ => mul_left_comm _ _ _)
  · rw [← smul_eq_mul, ← map_smul,
      map_integral_family (μ := μ) T hΦ (K := K) f.tsupport_subset hΦ0 φ (fun _ _ => rfl) _ hAvgΦ,
      map_integral_family (μ := μ) T hΨ (K := L) hρΩ hΨ0 ψ (fun _ _ => rfl) g (fun _ => rfl)]
    apply integral_congr_ae
    refine ae_of_all _ fun p => ?_
    let η : 𝓓(Ω, ℂ) := testOfCompact (K := L) hρΩ
      (hw.mul (f.contDiff.comp (LinearMap.toContinuousLinearMap (R p)).contDiff))
      (fun x hx => by rw [hw0 x hx, zero_mul])
    have hφ (x : E) : φ p x = η (R p⁻¹ x) := by
      change f x * w (R p⁻¹ x) = w (R p⁻¹ x) * f (R p (R p⁻¹ x))
      rw [← action_comp R, mul_inv_cancel, map_one, Module.End.one_apply, mul_comm]
    have hψ : ψ p = χ p⁻¹ • η := TestFunction.ext fun _ => rfl
    change T (ψ p) = T (φ p)
    rw [hψ, map_smul, smul_eq_mul, hT p⁻¹ η (φ p) hφ]

include he μ in
/-- A nonzero continuous covariant functional on a free open orbit is a nonzero
multiple of the character-weighted Haar integral along that orbit. -/
theorem exists_ne_zero_smul_orbitIntegral_of_covariance
    (hR : Continuous (fun p : H => LinearMap.toContinuousLinearMap (R p)))
    (χ : H →* ℂ) (hχ : Continuous χ) (T : 𝓓(Ω, ℂ) →L[ℂ] ℂ)
    (hT : IsCovariant R χ T) (hne : T ≠ 0) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ f : 𝓓(Ω, ℂ), T f = c * ∫ p, χ p⁻¹ * f (R p x₀) ∂μ := by
  classical
  obtain ⟨ρ, c, hρ, hρS, hρΩ, hc, hNorm⟩ := exists_normalized_cutoff R e x₀ he μ hR
  obtain ⟨f₀, hf₀⟩ : ∃ f₀, T f₀ ≠ 0 := by
    by_contra! h
    exact hne (ContinuousLinearMap.ext fun f => h f)
  have hcC : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  obtain ⟨g₀, hg₀, hT₀⟩ := transfer_test_integral R e x₀ he μ hR χ hχ f₀ hρ hρS hρΩ hNorm
  have hvalue {f : 𝓓(Ω, ℂ)} {g : 𝓓(Ω, ℂ)}
      (hg : ∀ x, g x = (ρ x : ℂ) * orbitIntegral R μ χ f x) (x : E) (hx : x ∈ Ω) :
      g x = (ρ x : ℂ) * (χ (e.symm ⟨x, hx⟩) *
        ((modularCharacterFun (e.symm ⟨x, hx⟩) : ℝ) • orbitIntegral R μ χ f x₀)) := by
    let q := e.symm ⟨x, hx⟩
    have hq : R q x₀ = x := (he q).symm.trans (congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩))
    rw [hg]
    exact congrArg ((ρ x : ℂ) * ·)
      ((congrArg (orbitIntegral R μ χ f) hq).symm.trans (orbitIntegral_coordinate R x₀ μ χ f q))
  have hF₀ : orbitIntegral R μ χ f₀ x₀ ≠ 0 := by
    intro hz
    have hg : g₀ = 0 := by
      ext x
      change g₀ x = 0
      by_cases hx : x ∈ Ω
      · simp only [hvalue hg₀ x hx, hz, smul_zero, mul_zero]
      · exact g₀.zero_on_compl hx
    have h := hT₀ T hT
    rw [hg, map_zero] at h
    exact (mul_ne_zero hcC hf₀) h.symm
  refine ⟨T f₀ / orbitIntegral R μ χ f₀ x₀, div_ne_zero hf₀ hF₀, fun f => ?_⟩
  obtain ⟨g, hg, hAvg⟩ := transfer_test_integral R e x₀ he μ hR χ hχ f hρ hρS hρΩ hNorm
  let z := orbitIntegral R μ χ f x₀ / orbitIntegral R μ χ f₀ x₀
  have hG : g = z • g₀ := by
    ext x
    change g x = z * g₀ x
    by_cases hx : x ∈ Ω
    · rw [hvalue hg x hx, hvalue hg₀ x hx]
      simp only [Complex.real_smul, z]
      field_simp [hF₀]
    · have hgz : g x = 0 := g.zero_on_compl hx
      have hg₀z : g₀ x = 0 := g₀.zero_on_compl hx
      rw [hgz, hg₀z, mul_zero]
  have hTF : T f = z * T f₀ := by
    apply mul_left_cancel₀ hcC
    rw [← hAvg T hT, hG, map_smul, smul_eq_mul, hT₀ T hT]
    ring
  change T f = (T f₀ / orbitIntegral R μ χ f₀ x₀) * orbitIntegral R μ χ f x₀
  rw [hTF]
  unfold z
  ring

include he μ in
/-- On a free open orbit, two continuous covariant test functionals with the same character
are proportional when the first one is nonzero. -/
theorem exists_proportional_of_covariance
    (hR : Continuous (fun p : H => LinearMap.toContinuousLinearMap (R p)))
    (χ : H →* ℂ) (hχ : Continuous χ) (T₁ T₂ : 𝓓(Ω, ℂ) →L[ℂ] ℂ)
    (h₁ : IsCovariant R χ T₁) (h₂ : IsCovariant R χ T₂) (hT₁ : T₁ ≠ 0) :
    ∃ d : ℂ, ∀ f, T₂ f = d * T₁ f := by
  by_cases hT₂ : T₂ = 0
  · exact ⟨0, fun f => by rw [hT₂, zero_apply, zero_mul]⟩
  obtain ⟨c₁, hc₁, hF₁⟩ := exists_ne_zero_smul_orbitIntegral_of_covariance R e x₀ he μ hR χ hχ T₁ h₁ hT₁
  obtain ⟨c₂, _, hF₂⟩ := exists_ne_zero_smul_orbitIntegral_of_covariance R e x₀ he μ hR χ hχ T₂ h₂ hT₂
  refine ⟨c₂ / c₁, fun f => ?_⟩
  rw [hF₂, hF₁, ← mul_assoc, div_mul_cancel₀ _ hc₁]

/-- A continuous linear action with a free open orbit has at most one
covariant continuous functional on the tests of that orbit, up to scale. -/
def SmoothOpenOrbitProportionalityStatement : Prop :=
  ∀ (H : Type u) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [T2Space H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (μ : Measure H) [μ.IsHaarMeasure] [μ.InnerRegular]
    (E : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Ω : Opens E) (R : H →* Module.End ℝ E) (e : H ≃ₜ (Ω : Set E)) (x₀ : E),
    (∀ q : H, (e q).val = R q x₀) →
    Continuous (fun p : H => LinearMap.toContinuousLinearMap (R p)) →
    ∀ (χ : H →* ℂ), Continuous χ →
    ∀ T₁ T₂ : 𝓓(Ω, ℂ) →L[ℂ] ℂ,
      IsCovariant R χ T₁ → IsCovariant R χ T₂ → T₁ ≠ 0 →
      ∃ d : ℂ, ∀ f, T₂ f = d * T₁ f

theorem smoothOpenOrbitProportionality : SmoothOpenOrbitProportionalityStatement.{u, v} := by
  intro H _ _ _ _ _ _ _ _ μ _ _ E _ _ _ Ω R e x₀ he
  exact exists_proportional_of_covariance R e x₀ he μ

end Langlands.Analysis.SmoothOpenOrbit

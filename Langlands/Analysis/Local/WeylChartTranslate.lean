import Langlands.Analysis.Local.WeylChartLocal

/-! # The local pushforward of the orbit map at an arbitrary base point -/

set_option linter.unusedSectionVars false

noncomputable section

namespace Langlands.Analysis.WeylChart

open Metric Set Topology MeasureTheory Measure Langlands.QuotientIntegration
open scoped NNReal ENNReal

universe u v

variable {F : Type u} [NontriviallyNormedField F] [CompleteSpace F] [IsUltrametricDist F]
  [ProperSpace F]
  {R : Type v} [NormedRing R] [NormedAlgebra F R] [FiniteDimensional F R] [CompleteSpace R]
  [IsUltrametricDist R] [MeasurableSpace R] [BorelSpace R]
  [MeasurableSpace Rˣ] [BorelSpace Rˣ]

/-- A unit is in regular position as soon as the kernel and the image of its adjoint defect
are complementary. -/
theorem isRegularPosition_of_isCompl {γ : Rˣ}
    (h : IsCompl (LinearMap.ker (defect F γ)) (LinearMap.range (defect F γ))) :
    IsRegularPosition F γ := by
  have hker : LinearMap.ker (defect F γ) = (centralizerAlg F γ).toSubmodule := by
    ext x
    exact mem_ker_defect_iff x
  unfold IsRegularPosition
  rw [← hker]
  exact h.symm

section Differential

variable {γ : Rˣ} (hγ : IsRegularPosition F γ)

/-- The derivative of the conjugation chart, read in the ambient coordinates. -/
def chartDifferential : R ≃L[F] R :=
  (coordCLE hγ).symm.trans (chartDerivative hγ)

/-- In ambient coordinates the derivative of the conjugation chart is the projection onto the
centralizer along the image of the adjoint defect, minus the adjoint defect. -/
theorem chartDifferential_eq
    (h : IsCompl (LinearMap.ker (defect F γ)) (LinearMap.range (defect F γ))) :
    (chartDifferential hγ).toLinearEquiv.toLinearMap =
      (LinearMap.ker (defect F γ)).projection (LinearMap.range (defect F γ)) h -
        defect F γ := by
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := (coordCLE hγ).surjective x
  have hker : (y.2 : R) ∈ LinearMap.ker (defect F γ) := (mem_ker_defect_iff _).2 y.2.property
  change chartDerivative hγ ((coordCLE hγ).symm (coordCLE hγ y)) = _
  rw [ContinuousLinearEquiv.symm_apply_apply, chartDerivative_apply, LinearMap.sub_apply,
    coordCLE_apply, map_add, map_add, Submodule.projection_apply_right h y.1,
    Submodule.projection_apply_of_mem_left h hker, LinearMap.mem_ker.1 hker, defect_apply]
  abel

/-- The chart scale is the scaling factor of ring Haar measure under the ambient differential. -/
theorem chartScale_eq_of_map {c : ℝ≥0}
    (h : (ringHaar hγ).map (chartDifferential hγ) = (c : ℝ≥0∞) • ringHaar hγ) :
    chartScale hγ = c := by
  have : ProperSpace R := FiniteDimensional.proper F R
  obtain ⟨r, hr⟩ := exists_isSmallRadius hγ
  have hmap : (coordHaar γ).map (chartDerivative hγ) =
      (ringHaar hγ).map (chartDifferential hγ) := by
    rw [ringHaar, Measure.map_map (chartDifferential hγ).continuous.measurable
      (coordCLE hγ).continuous.measurable]
    congr 1
    funext x
    change chartDerivative hγ x = chartDerivative hγ ((coordCLE hγ).symm (coordCLE hγ x))
    rw [ContinuousLinearEquiv.symm_apply_apply]
  have h2 := map_chartDerivative hγ
  rw [hmap, h] at h2
  have h3 := congrArg (fun ρ : Measure R => ρ (ringBall hγ r)) h2
  simp only [Measure.smul_apply, smul_eq_mul] at h3
  have h4 := (ENNReal.mul_left_inj (ringHaar_ringBall_ne_zero hγ hr)
    (ringHaar_ringBall_ne_top hγ hr)).1 h3
  exact (ENNReal.coe_inj.1 h4).symm

end Differential

/-- Right translation of the coset conjugates the orbit map. -/
theorem orbitMap_rightTranslate {H : Subgroup Rˣ} (hcomm : ∀ a b : H, a * b = b * a) (g : Rˣ)
    (p : LeftQuotient H × H) :
    orbitMap hcomm (rightTranslate H g p.1, p.2) = g⁻¹ * orbitMap hcomm p * g := by
  obtain ⟨q, h⟩ := p
  induction q using Quotient.inductionOn with
  | h x =>
    change (x * g)⁻¹ * (h : Rˣ) * (x * g) = g⁻¹ * (x⁻¹ * (h : Rˣ) * x) * g
    group

/-- Local pushforward of the orbit map at an arbitrary base point `(H g₀, t₀)`, for a
commutative subgroup `H` equal to the centralizer of the regular unit `t₀`. -/
theorem exists_orbitMap_localPushforward_of_eq {γ : Rˣ} (hγ : IsRegularPosition F γ)
    {H : Subgroup Rˣ} (hH : H = torusGroup γ) (hcomm : ∀ a b : H, a * b = b * a)
    [MeasurableSpace (LeftQuotient H)] [BorelSpace (LeftQuotient H)]
    (μ : Measure Rˣ) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (μT : Measure H) [μT.IsHaarMeasure] [μT.IsMulRightInvariant]
    (ν : Measure (LeftQuotient H)) (hν : IsCompatible H μ μT ν)
    (g₀ : Rˣ) (t₀ : H) (ht₀ : (t₀ : Rˣ) = γ)
    {N : Set (LeftQuotient H × H)} (hN : N ∈ 𝓝 (leftQuotientMap H g₀, t₀)) :
    ∃ W : Set (LeftQuotient H × H), W ⊆ N ∧ IsOpen W ∧ (leftQuotientMap H g₀, t₀) ∈ W ∧
      IsOpenEmbedding (fun z : W => orbitMap hcomm z.val) ∧
      ((ν.prod μT).restrict W).map (orbitMap hcomm) =
        (chartScale hγ : ℝ≥0∞) • μ.restrict (orbitMap hcomm '' W) := by
  subst hH
  obtain rfl : t₀ = ⟨γ, self_mem_torusGroup γ⟩ := Subtype.ext ht₀
  have : ProperSpace R := FiniteDimensional.proper F R
  have : LocallyCompactSpace Rˣ := Units.isOpenEmbedding_val.locallyCompactSpace
  have : SecondCountableTopology Rˣ :=
    Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology
  have hTclosed : IsClosed ((torusGroup γ : Subgroup Rˣ) : Set Rˣ) := by
    have hset : ((torusGroup γ : Subgroup Rˣ) : Set Rˣ) = {u | u * γ = γ * u} := by
      ext u
      change u ∈ torusGroup γ ↔ _
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Iff.rfl
    rw [hset]
    exact isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)
  have : LocallyCompactSpace (torusGroup γ) := hTclosed.locallyCompactSpace
  have : SecondCountableTopology (torusGroup γ) := IsInducing.subtypeVal.secondCountableTopology
  have : LocallyCompactSpace (LeftQuotient (torusGroup γ)) :=
    leftQuotient_locallyCompactSpace (torusGroup γ)
  have : SecondCountableTopology (LeftQuotient (torusGroup γ)) :=
    _root_.Topology.IsOpenQuotientMap.secondCountableTopology
      (leftQuotient_isOpenQuotientMap (torusGroup γ))
  have := hν.regular
  -- the translation of the source and the conjugation of the target
  set x₀ : LeftQuotient (torusGroup γ) × torusGroup γ :=
    (leftQuotientMap (torusGroup γ) 1, ⟨γ, self_mem_torusGroup γ⟩)
  let ΦM : (LeftQuotient (torusGroup γ) × torusGroup γ) ≃ᵐ
      (LeftQuotient (torusGroup γ) × torusGroup γ) :=
    (rightTranslate (torusGroup γ) g₀).toMeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
  let Φ : (LeftQuotient (torusGroup γ) × torusGroup γ) ≃ₜ
      (LeftQuotient (torusGroup γ) × torusGroup γ) :=
    (rightTranslate (torusGroup γ) g₀).prodCongr (Homeomorph.refl _)
  have hΦM : ⇑ΦM = ⇑Φ := rfl
  have hΦ0 : Φ x₀ = (leftQuotientMap (torusGroup γ) g₀, ⟨γ, self_mem_torusGroup γ⟩) := by
    change (rightTranslate (torusGroup γ) g₀ (leftQuotientMap (torusGroup γ) 1),
      (⟨γ, self_mem_torusGroup γ⟩ : torusGroup γ)) = _
    congr 1
    change Quotient.mk _ (1 * g₀) = Quotient.mk _ g₀
    rw [one_mul]
  let c : Rˣ ≃ᵐ Rˣ := (MeasurableEquiv.mulLeft g₀⁻¹).trans (MeasurableEquiv.mulRight g₀)
  have hc (u : Rˣ) : c u = g₀⁻¹ * u * g₀ := rfl
  have hcomp : orbitMap hcomm ∘ Φ = c ∘ orbitMap hcomm := by
    funext p
    exact orbitMap_rightTranslate hcomm g₀ p
  -- the patch at the identity coset
  have hN' : Φ ⁻¹' N ∈ 𝓝 x₀ :=
    Φ.continuous.continuousAt.preimage_mem_nhds (by rw [hΦ0]; exact hN)
  obtain ⟨W', hW'N, hW'o, hW'0, hW'emb, hW'map⟩ :=
    exists_orbitMap_localPushforward hγ hcomm μ μT ν hν hN'
  refine ⟨Φ '' W', ?_, Φ.isOpenMap _ hW'o, ⟨x₀, hW'0, hΦ0⟩, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact hW'N hz
  · -- the orbit map on the translated patch is a conjugate of the orbit map on the patch
    have hc' : IsOpenEmbedding (fun u : Rˣ => g₀⁻¹ * u * g₀) :=
      ((Homeomorph.mulLeft g₀⁻¹).trans (Homeomorph.mulRight g₀)).isOpenEmbedding
    have heq : (fun z : Φ '' W' => orbitMap hcomm z.val) =
        (fun u : Rˣ => g₀⁻¹ * u * g₀) ∘ (fun z : W' => orbitMap hcomm z.val) ∘
          (Φ.image W').symm := by
      funext z
      obtain ⟨z', rfl⟩ := (Φ.image W').surjective z
      simp only [Function.comp_apply, Homeomorph.symm_apply_apply]
      exact congrFun hcomp z'.val
    rw [heq]
    exact hc'.comp (hW'emb.comp (Φ.image W').symm.isOpenEmbedding)
  · -- transport of the measure identity
    have hpres : MeasurePreserving Φ (ν.prod μT) (ν.prod μT) :=
      (hν.right_invariant g₀).prod (MeasurePreserving.id μT)
    have hrestr : (ν.prod μT).restrict (Φ '' W') = ((ν.prod μT).restrict W').map Φ := by
      have h := ΦM.restrict_map (ν.prod μT) (Φ '' W')
      rw [hΦM, hpres.map_eq, Φ.injective.preimage_image] at h
      exact h
    have hcmeas : Measurable (orbitMap hcomm) := (continuous_orbitMap hcomm).measurable
    have hμc : μ.map c = μ := by
      change μ.map ((fun u => u * g₀) ∘ fun u => g₀⁻¹ * u) = μ
      rw [← Measure.map_map (measurable_mul_const g₀) (measurable_const_mul g₀⁻¹),
        map_mul_left_eq_self μ g₀⁻¹, map_mul_right_eq_self μ g₀]
    have himage : c '' (orbitMap hcomm '' W') = orbitMap hcomm '' (Φ '' W') := by
      rw [image_image, image_image]
      exact image_congr fun p _ => (congrFun hcomp p).symm
    have hcres : (μ.restrict (orbitMap hcomm '' W')).map c =
        μ.restrict (c '' (orbitMap hcomm '' W')) := by
      have h := c.restrict_map μ (c '' (orbitMap hcomm '' W'))
      rw [hμc, c.injective.preimage_image] at h
      exact h.symm
    rw [hrestr, Measure.map_map hcmeas Φ.continuous.measurable, hcomp,
      ← Measure.map_map c.measurable hcmeas, hW'map, Measure.map_smul, hcres, himage]
    exact c.measurable.aemeasurable

import Langlands.Representation.Archimedean.CompactSmoothApproximation
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-! # Gårding averages are dense in the genuine smooth-vector topology -/

noncomputable section
set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped Manifold ContDiff

namespace Langlands.Archimedean

open CompactSmoothAverage

universe uA uG uE

private theorem integral_comap_subtype_eq_integral
    {X B : Type*} [MeasurableSpace X] [NormedAddCommGroup B] [NormedSpace ℝ B]
    (μ : Measure X) {K : Set X} (hK : MeasurableSet K) (f : X → B)
    (h0 : ∀ x, x ∉ K → f x = 0) :
    (∫ x : K, f x ∂μ.comap Subtype.val) = ∫ x, f x ∂μ :=
  (integral_subtype_comap hK f).trans (setIntegral_eq_integral_of_forall_compl_eq_zero h0)

variable {A : Type uA} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace A G]
  [LieGroup 𝓘(ℝ, A) ∞ G] [T2Space G] [LocallyCompactSpace G] [SigmaCompactSpace G]
  [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]

/-- Smooth normalized nonnegative weights supported in an arbitrary
identity neighborhood. -/
theorem exists_normalizedSmoothWeight (U : Set G) (hU : U ∈ 𝓝 (1 : G)) :
    ∃ φ : G → ℂ, ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, ℂ) ∞ φ ∧ HasCompactSupport φ ∧
      tsupport φ ⊆ U ∧ (∫ x, φ x ∂μ) = 1 ∧ (∫ x, ‖φ x‖ ∂μ) = 1 := by
  obtain ⟨V, hVU, hVo, hV₁⟩ := mem_nhds_iff.mp hU
  obtain ⟨K, hK, h₁, hKV⟩ := exists_compact_subset hVo hV₁
  obtain ⟨f, hfs, hfd, hfpos⟩ :=
    isOpen_interior.exists_contMDiff_support_eq (n := (⊤ : ℕ∞)) (𝓘(ℝ, A)) (s := interior K)
  have hfsK : tsupport f ⊆ K := closure_minimal (by rw [hfs]; exact interior_subset) hK.isClosed
  have hfc : HasCompactSupport f := hK.of_isClosed_subset isClosed_closure hfsK
  have hf₁ : f 1 ≠ 0 := by
    rw [← hfs] at h₁
    exact h₁
  have hi : 0 < ∫ x, f x ∂μ :=
    hfd.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hfc hfpos hf₁
  let c := (∫ x, f x ∂μ)⁻¹
  have hc : 0 < c := inv_pos.mpr hi
  let φ : G → ℂ := fun x => ((c * f x : ℝ) : ℂ)
  have hφd : ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, ℂ) ∞ φ :=
    Complex.ofRealCLM.contDiff.contMDiff.comp (contMDiff_const.mul hfd)
  have hφK : tsupport φ ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro x hx
    apply interior_subset
    rw [← hfs]
    exact fun h0 => hx (by simp only [φ, h0, mul_zero, Complex.ofReal_zero])
  refine ⟨φ, hφd, hK.of_isClosed_subset isClosed_closure hφK, hφK.trans (hKV.trans hVU),
    ?_, ?_⟩
  · change (∫ x, ((c * f x : ℝ) : ℂ) ∂μ) = 1
    rw [integral_complex_ofReal, integral_const_mul, show c = (∫ x, f x ∂μ)⁻¹ from rfl,
      inv_mul_cancel₀ hi.ne', Complex.ofReal_one]
  · have hnorm (x : G) : ‖φ x‖ = c * f x := by
      change ‖((c * f x : ℝ) : ℂ)‖ = _
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hc.le (hfpos x))]
    simp_rw [hnorm]
    rw [integral_const_mul, show c = (∫ x, f x ∂μ)⁻¹ from rfl, inv_mul_cancel₀ hi.ne']

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  (π : G →* (E →L[ℂ] E))

/-- Smooth vectors given by integrating an orbit against one compactly
supported smooth kernel with the supplied Haar measure. -/
def IsGardingAverage (v : DerivativeSmoothVectors 𝓘(ℝ, A) π) : Prop :=
  ∃ (φ : G → ℂ), ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, ℂ) ∞ φ ∧ HasCompactSupport φ ∧ ∃ w : E,
    (DerivativeSmoothVectors.toSmooth 𝓘(ℝ, A) π v).val = ∫ x, φ x • π x w ∂μ

/-- Actual Gårding averages of smooth vectors approximate every smooth
vector in all its genuine word-derivative seminorms simultaneously. -/
theorem dense_gardingAverages : Dense {v : DerivativeSmoothVectors 𝓘(ℝ, A) π |
    IsGardingAverage (A := A) μ π v} := by
  intro v
  apply mem_closure_iff_nhds.mpr
  intro V hV
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds (1 : G)
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let μK := μ.comap (Subtype.val : K → G)
  let : IsFiniteMeasure μK := ⟨by
    have e := MeasurableEmbedding.subtype_coe hK.measurableSet
    change (μ.comap (Subtype.val : K → G)) univ < ⊤
    rw [e.comap_apply, image_univ, Subtype.range_coe_subtype]
    exact hK.measure_lt_top⟩
  let j : C(K, G) := ⟨Subtype.val, continuous_subtype_val⟩
  let w := (DerivativeSmoothVectors.toSmooth 𝓘(ℝ, A) π v).val
  have hw : IsSmoothVector 𝓘(ℝ, A) π w :=
    (DerivativeSmoothVectors.toSmooth 𝓘(ℝ, A) π v).property
  let aFamily (g : G) : E := π g w
  have hfamily : ContMDiff (𝓘(ℝ, A).prod 𝓘(ℝ, A)) 𝓘(ℝ, E) ∞
      (fun p : G × G => π p.1 (aFamily p.2)) := by
    have hmult : ContMDiff (𝓘(ℝ, A).prod 𝓘(ℝ, A)) 𝓘(ℝ, A) ∞
        (fun p : G × G => p.1 * p.2) := contMDiff_fst.mul contMDiff_snd
    have h := (show ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, E) ∞ (orbitMap π w) from hw).comp hmult
    have he : orbitMap π w ∘ (fun p : G × G => p.1 * p.2) =
        (fun p : G × G => π p.1 (aFamily p.2)) := by
      funext p
      exact congrArg (fun L : E →L[ℂ] E => L w) (map_mul π p.1 p.2)
    exact he ▸ h
  have hbase : derivativeFamily π hfamily 1 = v := by
    apply (DerivativeSmoothVectors.toSmooth 𝓘(ℝ, A) π).injective
    apply Subtype.ext
    simp only [derivativeFamily, LinearEquiv.apply_symm_apply, aFamily, map_one, one_apply_eq_self, w]
  obtain ⟨U, hU, hAvg⟩ := exists_average_neighborhood π hfamily μK (1 : G) V (hbase.symm ▸ hV)
  have hUI : U ∩ interior K ∈ 𝓝 (1 : G) :=
    inter_mem hU (isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hKn))
  obtain ⟨φ, hφd, hφc, hφsupp, hφ, hφnorm⟩ := exists_normalizedSmoothWeight (A := A) μ _ hUI
  have hzero (x : G) (hx : x ∉ K) : φ x = 0 := by
    by_contra hh
    exact hx (interior_subset (hφsupp (subset_closure (show x ∈ Function.support φ from hh))).2)
  let a : C(K, ℂ) := ⟨fun x => φ x, hφd.continuous.comp continuous_subtype_val⟩
  have ha (x : K) (hx : a x ≠ 0) : j x ∈ U :=
    (hφsupp (subset_closure (show (x : G) ∈ Function.support φ from hx))).1
  have hai : (∫ x : K, a x ∂μK) = 1 :=
    (integral_comap_subtype_eq_integral μ hK.measurableSet φ hzero).trans hφ
  have han : (∫ x : K, ‖a x‖ ∂μK) = 1 :=
    (integral_comap_subtype_eq_integral μ hK.measurableSet (fun x => ‖φ x‖)
      (fun x hx => by rw [hzero x hx, norm_zero])).trans hφnorm
  refine ⟨weightAverageLM π μK j hfamily a, hAvg a j ha hai han, φ, hφd, hφc, w, ?_⟩
  simp only [weightAverageLM, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.apply_symm_apply]
  exact integral_comap_subtype_eq_integral μ hK.measurableSet (fun x => φ x • π x w)
    (fun x hx => by rw [hzero x hx, zero_smul])

set_option backward.isDefEq.respectTransparency false in
omit [SigmaCompactSpace G] in
private theorem gardingIntegral_at (hπ : IsContinuousRepresentation π)
    (φ : G → ℂ) (hφd : ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, ℂ) ∞ φ)
    (hφc : HasCompactSupport φ) (v : E) (g₀ : G) :
    let orbit := orbitMap π (∫ x, φ x • π x v ∂μ)
    ContMDiffAt 𝓘(ℝ, A) 𝓘(ℝ, E) ∞ orbit g₀ ∧
      ∀ X : A, @Eq E (mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) orbit g₀ X)
        (∫ y, (show ℂ from mfderiv 𝓘(ℝ, A) 𝓘(ℝ, ℂ)
          (fun x => φ (x⁻¹ * y)) g₀ X) • π y v ∂μ) := by
  have hmul : ContMDiff (𝓘(ℝ, A).prod 𝓘(ℝ, A)) 𝓘(ℝ, A) ∞
      (fun p : G × G => p.1 * p.2) := contMDiff_fst.mul contMDiff_snd
  have hinv : ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, A) ∞ (fun g : G => g⁻¹) :=
    contMDiff_id.inv
  let : IsTopologicalGroup G :=
    { continuous_mul := hmul.continuous
      continuous_inv := hinv.continuous }
  have hv : Continuous (fun x : G => π x v) := hπ.comp (continuous_id.prodMk continuous_const)
  have hi : Integrable (fun x => φ x • π x v) μ :=
    (hφd.continuous.smul hv).integrable_of_hasCompactSupport hφc.smul_right
  have htrans (g : G) : orbitMap π (∫ x, φ x • π x v ∂μ) g =
      ∫ y, φ (g⁻¹ * y) • π y v ∂μ := by
    change π g (∫ x, φ x • π x v ∂μ) = _
    rw [← (π g).integral_comp_comm hi]
    have hm : MeasurePreserving (fun x => g * x) μ μ :=
      ⟨(continuous_const_mul g).measurable, map_mul_left_eq_self μ g⟩
    have he : MeasurableEmbedding (fun x => g * x) :=
      (Homeomorph.mulLeft g).toMeasurableEquiv.measurableEmbedding
    have h := hm.integral_comp he (fun y => φ (g⁻¹ * y) • π y v)
    simpa only [map_smul, map_mul, mul_apply_eq_comp, Function.comp_apply, inv_mul_cancel_left]
      using h
  dsimp only
  rw [funext htrans]
  obtain ⟨U, hUc, hUg⟩ := exists_compact_mem_nhds g₀
  let K : Set G := (fun p : G × G => p.1 * p.2) '' (U ×ˢ tsupport φ)
  have hK : IsCompact K := (hUc.prod hφc).image continuous_mul
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let μK := μ.comap (Subtype.val : K → G)
  let : IsFiniteMeasure μK := ⟨by
    have e := MeasurableEmbedding.subtype_coe hK.measurableSet
    change (μ.comap (Subtype.val : K → G)) univ < ⊤
    rw [e.comap_apply, image_univ, Subtype.range_coe_subtype]
    exact hK.measure_lt_top⟩
  let : ChartedSpace (A × E) (G × E) := prodChartedSpace A G E E
  let : IsManifold 𝓘(ℝ, A × E) ∞ (G × E) := by
    rw [modelWithCornersSelf_prod]
    exact inferInstanceAs (IsManifold (𝓘(ℝ, A).prod 𝓘(ℝ, E)) ∞ (G × E))
  let j : C(K, G × E) :=
    ⟨fun y => (y.val, π y.val v), continuous_subtype_val.prodMk (hv.comp continuous_subtype_val)⟩
  let H (p : G × (G × E)) := φ (p.1⁻¹ * p.2.1) • p.2.2
  have hH : ContMDiff (𝓘(ℝ, A).prod 𝓘(ℝ, A × E)) 𝓘(ℝ, E) ∞ H := by
    have h₁ : ContMDiff 𝓘(ℝ, A × E) 𝓘(ℝ, A) ∞ (Prod.fst : G × E → G) := by
      rw [modelWithCornersSelf_prod]
      exact contMDiff_fst
    have h₂ : ContMDiff 𝓘(ℝ, A × E) 𝓘(ℝ, E) ∞ (Prod.snd : G × E → E) := by
      rw [modelWithCornersSelf_prod]
      exact contMDiff_snd
    have hs : ContMDiff (𝓘(ℝ, ℂ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
        (fun p : ℂ × E => p.1 • p.2) := by
      rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
      exact contDiff_smul.contMDiff
    exact hs.comp ((hφd.comp (contMDiff_fst.inv.mul (h₁.comp contMDiff_snd))).prodMk
      (h₂.comp contMDiff_snd))
  have hI := Langlands.Analysis.CompactManifoldVectorIntegral.contMDiff_weightedIntegral
    μK (1 : C(K, ℂ)) j hH
  have hzero (g : G) (hg : g ∈ U) (y : G) (hy : y ∉ K) : φ (g⁻¹ * y) = 0 := by
    by_contra hn
    exact hy ⟨(g, g⁻¹ * y), ⟨hg, subset_closure hn⟩, mul_inv_cancel_left g y⟩
  have heq : (fun g => ∫ y, φ (g⁻¹ * y) • π y v ∂μ) =ᶠ[𝓝 g₀]
      (fun g => ∫ y : K, (1 : C(K, ℂ)) y • H (g, j y) ∂μK) := by
    filter_upwards [hUg] with g hg
    change (∫ y, φ (g⁻¹ * y) • π y v ∂μ) =
      ∫ y : K, (1 : ℂ) • (φ (g⁻¹ * (y : G)) • π y v) ∂μK
    simp only [one_smul]
    exact (integral_comap_subtype_eq_integral μ hK.measurableSet _
      (fun y hy => by rw [hzero g hg y hy, zero_smul])).symm
  refine ⟨(hI g₀).congr_of_eventuallyEq heq, fun X => ?_⟩
  rw [heq.mfderiv_eq]
  refine (Langlands.Analysis.CompactManifoldVectorIntegral.mfderiv_weightedIntegral_apply
    μK (1 : C(K, ℂ)) j hH g₀ X).trans ?_
  let F (y : G) : E := (show ℂ from mfderiv 𝓘(ℝ, A) 𝓘(ℝ, ℂ)
    (fun g => φ (g⁻¹ * y)) g₀ X) • π y v
  have hF (y : G) : @Eq E (mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E)
      (fun g => φ (g⁻¹ * y) • π y v) g₀ X) (F y) := by
    let L := ((ContinuousLinearMap.id ℂ ℂ).smulRight (π y v)).restrictScalars ℝ
    have hL : ∀ z : ℂ, L z = z • π y v := fun _ => rfl
    have hφy : MDifferentiableAt 𝓘(ℝ, A) 𝓘(ℝ, ℂ) (fun g => φ (g⁻¹ * y)) g₀ :=
      ((hφd.comp (hinv.mul contMDiff_const)) g₀).mdifferentiableAt (by simp)
    rw [show (fun g => φ (g⁻¹ * y) • π y v) = L ∘ (fun g => φ (g⁻¹ * y)) from
      (funext fun g => (hL (φ (g⁻¹ * y))).symm),
      mfderiv_comp g₀ L.differentiableAt.mdifferentiableAt hφy, ContinuousLinearMap.mfderiv_eq]
    rfl
  calc
    _ = ∫ y : K, F y ∂μK := by
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      change (1 : ℂ) • (show E from mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E)
        (fun g => φ (g⁻¹ * (y : G)) • π y v) g₀ X) = F y
      rw [one_smul, hF]
    _ = ∫ y, F y ∂μ := by
      apply integral_comap_subtype_eq_integral μ hK.measurableSet
      intro y hy
      have hz : (fun g => φ (g⁻¹ * y)) =ᶠ[𝓝 g₀] (fun _ : G => (0 : ℂ)) := by
        filter_upwards [hUg] with g hg using hzero g hg y hy
      change (show ℂ from mfderiv 𝓘(ℝ, A) 𝓘(ℝ, ℂ)
        (fun g => φ (g⁻¹ * y)) g₀ X) • π y v = 0
      rw [hz.mfderiv_eq, mfderiv_const, ContinuousLinearMap.comp_zero]
      change (0 : ℂ) • π y v = 0
      exact zero_smul ℂ (π y v)

omit [SigmaCompactSpace G] in
/-- Averaging any vector against a smooth compactly supported kernel
gives a genuine smooth vector for a continuous representation. -/
theorem isSmoothVector_gardingIntegral (hπ : IsContinuousRepresentation π)
    (φ : G → ℂ) (hφd : ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, ℂ) ∞ φ)
    (hφc : HasCompactSupport φ) (v : E) :
    IsSmoothVector 𝓘(ℝ, A) π (∫ x, φ x • π x v ∂μ) :=
  fun g => (gardingIntegral_at μ π hπ φ hφd hφc v g).1

omit [SigmaCompactSpace G] in
/-- A genuine representation derivative of the average is obtained by
differentiating the left-translated kernel at the identity. -/
theorem lieDerivative_gardingIntegral (hπ : IsContinuousRepresentation π)
    (φ : G → ℂ) (hφd : ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, ℂ) ∞ φ)
    (hφc : HasCompactSupport φ) (v : E) (X : A) :
    lieDerivative 𝓘(ℝ, A) π X (∫ x, φ x • π x v ∂μ) =
      ∫ y, (show ℂ from mfderiv 𝓘(ℝ, A) 𝓘(ℝ, ℂ)
        (fun x => φ (x⁻¹ * y)) 1 X) • π y v ∂μ :=
  (gardingIntegral_at μ π hπ φ hφd hφc v 1).2 X

end Langlands.Archimedean

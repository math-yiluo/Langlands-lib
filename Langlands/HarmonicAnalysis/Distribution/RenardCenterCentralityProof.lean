import Langlands.HarmonicAnalysis.Distribution.RenardCenterCriteriaProof
import Langlands.HarmonicAnalysis.Distribution.RenardEssentialProductsStatements

/-! # Renard II.3.13: centrality, Hecke commutation and conjugation invariance -/

noncomputable section

open MeasureTheory

namespace Langlands.HarmonicAnalysis.Distribution.RenardCenter

universe uG

section Formulas

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]

/-- `T * h` evaluates `T` on the test `x ↦ ∫ h(z) f(xz) dμ(z)`. -/
theorem rightHeckeConvolution_eq (T : Distribution G) (h : Hecke.HeckeAlgebra μ)
    (f F : SchwartzBruhat G) (hF : ∀ x, F x = ∫ z, h z * f (x * z) ∂μ) :
    rightHeckeConvolution μ T h f = T F := by
  rw [rightHeckeConvolution_apply]
  congr 1
  ext x
  rw [hF, Hecke.TestFunction.convolution_apply]
  refine Eq.trans (integral_mul_left_eq_self _ x).symm ?_
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [Hecke.TestFunction.inversion_apply, mul_inv_rev, inv_mul_cancel_right, inv_inv]
  exact mul_comm _ _

/-- `h * T` evaluates `T` on the test `x ↦ ∫ h(y) f(yx) dμ(y)`; the inverse
measure in the published left action is undone by inversion. -/
theorem leftHeckeConvolution_eq (T : Distribution G) (h : Hecke.HeckeAlgebra μ)
    (f F : SchwartzBruhat G) (hF : ∀ x, F x = ∫ y, h y * f (y * x) ∂μ) :
    leftHeckeConvolution μ h T f = T F := by
  rw [leftHeckeConvolution_apply]
  congr 1
  ext x
  rw [hF, Hecke.TestFunction.convolution_apply, Measure.inv_def,
    integral_map measurable_inv.aemeasurable]
  · apply integral_congr_ae
    filter_upwards [] with y
    simp only [Hecke.TestFunction.inversion_apply, inv_inv]
    rfl
  · exact ((Hecke.TestFunction.inversion (Hecke.HeckeAlgebra.toTestFunction μ h)).continuous.mul
      (f.continuous.comp (continuous_inv.mul continuous_const))).aestronglyMeasurable

end Formulas

section Commutation

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
variable [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]

/-- A distribution is determined by its right products with Hecke elements. -/
theorem eq_of_rightHeckeConvolution_eq (D D' : Distribution G)
    (hD : ∀ h : Hecke.HeckeAlgebra μ,
      rightHeckeConvolution μ D h = rightHeckeConvolution μ D' h) : D = D' := by
  classical
  apply LinearMap.ext
  intro f
  obtain ⟨K, -, hKc, hK⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance G {f} ⊤
  have hf := hK f (by simp)
  let e : Hecke.HeckeAlgebra μ := Hecke.HeckeAlgebra.normalizedIndicator μ K hKc
  have key : ∀ E : Distribution G, rightHeckeConvolution μ E e f = E f := by
    intro E
    apply rightHeckeConvolution_eq μ E e f f
    intro x
    have := integral_leftTranslate_indicator μ K hKc 1 (fun z => f (x * z))
      (fun k hk => by simpa using hf.2 ⟨k, hk⟩ x)
    simpa [e, Hecke.HeckeAlgebra.normalizedIndicator_apply] using this.symm
  rw [← key D, ← key D', hD]

omit [MeasurableSpace G] [BorelSpace G] in
/-- A sampling level adapted to both Hecke kernels `f(xz)` and `f(yx)`. -/
theorem exists_sampling_level_two_sided (f h : SchwartzBruhat G) :
    ∃ K : OpenSubgroup G,
      (∀ (k : K) g, h (g * (k : G)) = h g) ∧
      (∀ (k : K) x, f (x * (k : G)) = f x) ∧
      (∀ y, h y ≠ 0 → ∀ (k : K) x, f ((y * (k : G) * y⁻¹) * x) = f x) := by
  classical
  obtain ⟨K₀, -, -, hK₀⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance G {f, h} ⊤
  have hf0 := hK₀ f (by simp)
  have hh0 := hK₀ h (by simp)
  obtain ⟨U, hU⟩ := exists_openSubgroup_conj_mem (Function.support (h : G → ℂ))
    (Hecke.TestFunction.isCompact_support h) K₀
  refine ⟨K₀ ⊓ U, ?_, ?_, ?_⟩
  · intro k g
    exact hh0.2 ⟨k, (OpenSubgroup.mem_inf.1 k.2).1⟩ g
  · intro k x
    exact hf0.2 ⟨k, (OpenSubgroup.mem_inf.1 k.2).1⟩ x
  · intro y hy k x
    exact hf0.1 ⟨y * k * y⁻¹, hU y hy k (OpenSubgroup.mem_inf.1 k.2).2⟩ x

/-- Translation invariance implies commutation with every Hecke element. -/
theorem commute_of_translation (T : Distribution G) (hT : TranslationCondition T)
    (h : Hecke.HeckeAlgebra μ) :
    rightHeckeConvolution μ T h = leftHeckeConvolution μ h T := by
  classical
  apply LinearMap.ext
  intro f
  let h' : SchwartzBruhat G := Hecke.HeckeAlgebra.toTestFunction μ h
  obtain ⟨K, hh, hfr, hfl⟩ := exists_sampling_level_two_sided f h'
  let S := Hecke.fixedLevelActionSamples μ K h' hh
  rw [rightHeckeConvolution_eq μ T h f
      (∑ i, sampleWeight μ K h' hh i • Hecke.TestFunction.rightTranslate (S.points i) f) ?_,
    leftHeckeConvolution_eq μ T h f
      (∑ i, sampleWeight μ K h' hh i • Hecke.TestFunction.leftTranslate (S.points i)⁻¹ f) ?_]
  · rw [map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, map_smul, hT, inv_inv]
  · intro x
    change _ = ∫ y, h' y * f (y * x) ∂μ
    rw [integral_eq_sampleWeight μ K h' hh (fun y => f (y * x))]
    · simp [S, Finset.sum_apply]
    · intro y hy k
      have := hfl y hy k (y * x)
      simpa [mul_assoc] using this
  · intro x
    change _ = ∫ z, h' z * f (x * z) ∂μ
    rw [integral_eq_sampleWeight μ K h' hh (fun z => f (x * z))]
    · simp [S, Finset.sum_apply]
    · intro y _ k
      simpa [mul_assoc] using hfr k (x * y)

/-- Commutation with the normalized indicator of `g⁻¹K`, for `K` small,
is the translation identity at `g`. -/
theorem translation_of_commute (T : Distribution G)
    (hT : ∀ h : Hecke.HeckeAlgebra μ,
      rightHeckeConvolution μ T h = leftHeckeConvolution μ h T) :
    TranslationCondition T := by
  classical
  intro g f
  obtain ⟨K₀, -, -, hK₀⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance G {f} ⊤
  have hf0 := hK₀ f (by simp)
  obtain ⟨K, hKle, hKc, -⟩ :=
    Hecke.TestFunction.commonCompactOpenBiInvariance G ∅ (K₀ ⊓ conjPreimage g⁻¹ K₀)
  let h : Hecke.HeckeAlgebra μ := ((μ.real (K : Set G) : ℂ)⁻¹) •
    Hecke.TestFunction.leftTranslate g⁻¹ (Hecke.TestFunction.subgroupIndicator K hKc)
  have hval : ∀ y, h y = (μ.real (K : Set G) : ℂ)⁻¹ *
      (K : Set G).indicator (fun _ => (1 : ℂ)) (g⁻¹⁻¹ * y) := fun y => rfl
  have e1 : rightHeckeConvolution μ T h f = T (Hecke.TestFunction.rightTranslate g⁻¹ f) := by
    apply rightHeckeConvolution_eq
    intro x
    rw [Hecke.TestFunction.rightTranslate_apply]
    simp only [hval]
    refine (integral_leftTranslate_indicator μ K hKc g⁻¹ (fun z => f (x * z)) ?_).symm
    intro k hk
    have hk' := OpenSubgroup.mem_inf.1 (hKle hk)
    simpa [mul_assoc] using hf0.2 ⟨k, hk'.1⟩ (x * g⁻¹)
  have e2 : leftHeckeConvolution μ h T f = T (Hecke.TestFunction.leftTranslate g f) := by
    apply leftHeckeConvolution_eq
    intro x
    rw [Hecke.TestFunction.leftTranslate_apply]
    simp only [hval]
    refine (integral_leftTranslate_indicator μ K hKc g⁻¹ (fun y => f (y * x)) ?_).symm
    intro k hk
    have hk' := OpenSubgroup.mem_inf.1 (hKle hk)
    have hc : g⁻¹ * k * g⁻¹⁻¹ ∈ K₀ := mem_conjPreimage.1 hk'.2
    have := hf0.1 ⟨g⁻¹ * k * g⁻¹⁻¹, hc⟩ (g⁻¹ * x)
    simpa [mul_assoc] using this
  have := LinearMap.congr_fun (hT h) f
  rw [e1, e2] at this
  exact this.symm

/-- Hecke commutation is equivalent to conjugation invariance, for every
algebraic distribution. -/
theorem commute_iff_isConjugationInvariant (T : Distribution G) :
    (∀ h : Hecke.HeckeAlgebra μ,
      rightHeckeConvolution μ T h = leftHeckeConvolution μ h T) ↔
      IsConjugationInvariant T :=
  ⟨fun hc => (isConjugationInvariant_iff_translation T).2 (translation_of_commute μ T hc),
    fun hT => commute_of_translation μ T ((isConjugationInvariant_iff_translation T).1 hT)⟩

/-- The centrality specification holds for every right product satisfying the
published right-product specification. -/
theorem centrality
    (pr : rightEssentiallyCompact μ →ₗ[ℂ]
      rightEssentiallyCompact μ →ₗ[ℂ] rightEssentiallyCompact μ)
    (hpr : RenardEssentialProducts.RightProductSpecification μ pr) :
    CentralitySpecification μ pr := by
  obtain ⟨⟨hassoc, -, -, hhecke⟩, -, hright⟩ := hpr
  have lift : ∀ (h : Hecke.HeckeAlgebra μ) (H : rightEssentiallyCompact μ),
      (H : Distribution G) = heckeDistribution μ h → ∀ S : rightEssentiallyCompact μ,
        (pr S H : Distribution G) = rightHeckeConvolution μ (S : Distribution G) h ∧
        (pr H S : Distribution G) = leftHeckeConvolution μ h (S : Distribution G) := by
    intro h H hH S
    obtain ⟨H', hH', h1, h2⟩ := hhecke S h
    have : H' = H := Subtype.ext (hH'.trans hH.symm)
    subst this
    exact ⟨h1, h2⟩
  intro T
  refine ⟨⟨?_, ?_⟩, commute_iff_isConjugationInvariant μ T, ?_⟩
  · intro hc h
    obtain ⟨H, -, h1, h2⟩ := hhecke T h
    rw [← h1, ← h2, hc H]
  · intro hc U
    apply Subtype.ext
    apply eq_of_rightHeckeConvolution_eq μ
    intro h
    obtain ⟨H, hH, -, -⟩ := hhecke T h
    rw [← (lift h H hH (pr T U)).1, ← (lift h H hH (pr U T)).1]
    congr 1
    rw [hassoc, hassoc]
    obtain ⟨k, hk, -⟩ := hright T U h
    have hUH : (pr U H : Distribution G) = heckeDistribution μ k :=
      (lift h H hH U).1.trans hk.symm
    have hTH : pr T H = pr H T := Subtype.ext (by
      rw [(lift h H hH T).1, (lift h H hH T).2, hc h])
    rw [hTH, ← hassoc U H T]
    apply Subtype.ext
    rw [(lift k _ hUH T).1, (lift k _ hUH T).2, hc k]
  · intro hconj
    refine Submodule.mem_inf.2 ⟨T.2, fun h => ?_⟩
    rw [← (commute_iff_isConjugationInvariant μ T).2 hconj h]
    exact T.2 h

end Commutation

end Langlands.HarmonicAnalysis.Distribution.RenardCenter

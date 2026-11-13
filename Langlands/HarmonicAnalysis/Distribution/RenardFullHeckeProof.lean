import Langlands.HarmonicAnalysis.Distribution.RenardFullHeckeStatements
import Langlands.HarmonicAnalysis.Distribution.RenardUniformDensityProof

/-! # Renard II.3.13: proof of the full-distribution Hecke action laws -/

noncomputable section

open MeasureTheory
open scoped Pointwise

namespace Langlands.HarmonicAnalysis.Distribution.RenardFullHecke

universe uG

open GroupFunctionSpaces

section Kernels

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [IsFiniteMeasureOnCompacts μ]

/-- The test transposed by the right action, `x ↦ ∫ a(y) f(xy) dμ(y)`, written as
the convolution occurring in `rightHeckeOperator`. -/
def rightKernel (a f : SchwartzBruhat G) : SchwartzBruhat G :=
  Hecke.TestFunction.convolution μ f (Hecke.TestFunction.inversion a)

/-- The test transposed by the left action, `x ↦ ∫ a(y) f(yx) dμ(y)`, written as
the convolution against the inverted measure occurring in `leftHeckeOperator`. -/
def leftKernel (a f : SchwartzBruhat G) : SchwartzBruhat G :=
  Hecke.TestFunction.convolution μ.inv (Hecke.TestFunction.inversion a) f

theorem rightHeckeConvolution_eq_kernel (T : Distribution G) (h : Hecke.HeckeAlgebra μ)
    (f : SchwartzBruhat G) :
    rightHeckeConvolution μ T h f =
      T (rightKernel μ (Hecke.HeckeAlgebra.toTestFunction μ h) f) := rfl

theorem leftHeckeConvolution_eq_kernel (h : Hecke.HeckeAlgebra μ) (T : Distribution G)
    (f : SchwartzBruhat G) :
    leftHeckeConvolution μ h T f =
      T (leftKernel μ (Hecke.HeckeAlgebra.toTestFunction μ h) f) := rfl

omit [IsFiniteMeasureOnCompacts μ] in
/-- Integration against the inverted measure is integration of the inverted function. -/
theorem integral_inv_measure (F : G → ℂ) : ∫ y, F y ∂μ.inv = ∫ y, F y⁻¹ ∂μ := by
  have he : MeasurableEmbedding fun x : G => x⁻¹ :=
    (MeasurableEquiv.inv G).measurableEmbedding
  rw [Measure.inv_def]
  exact he.integral_map F

omit [IsFiniteMeasureOnCompacts μ] in
theorem leftKernel_apply (a f : SchwartzBruhat G) (x : G) :
    leftKernel μ a f x = ∫ y, a y * f (y * x) ∂μ := by
  change (∫ y, a y⁻¹ * f (y⁻¹ * x) ∂μ.inv) = _
  rw [integral_inv_measure]
  simp only [inv_inv]

variable [μ.IsMulLeftInvariant]

omit [IsFiniteMeasureOnCompacts μ] in
theorem rightKernel_apply (a f : SchwartzBruhat G) (x : G) :
    rightKernel μ a f x = ∫ y, a y * f (x * y) ∂μ := by
  change (∫ y, f y * a ((y⁻¹ * x)⁻¹) ∂μ) = _
  rw [← integral_mul_left_eq_self (fun y => f y * a ((y⁻¹ * x)⁻¹)) x]
  congr 1
  funext y
  simp only [mul_inv_rev, inv_inv, inv_mul_cancel_right]
  ring

omit [IsFiniteMeasureOnCompacts μ] in
/-- Inversion reverses left-Haar convolution of inverted tests; no modular factor
occurs because both inversions are applied to the factors. -/
theorem convolution_inversion (a b : SchwartzBruhat G) :
    Hecke.TestFunction.convolution μ (Hecke.TestFunction.inversion a)
        (Hecke.TestFunction.inversion b) =
      Hecke.TestFunction.inversion (Hecke.TestFunction.convolution μ b a) := by
  ext x
  change (∫ y, a y⁻¹ * b ((y⁻¹ * x)⁻¹) ∂μ) = ∫ y, b y * a (y⁻¹ * x⁻¹) ∂μ
  rw [← integral_mul_left_eq_self (fun y => b y * a (y⁻¹ * x⁻¹)) x⁻¹]
  congr 1
  funext y
  simp only [mul_inv_rev, inv_inv, mul_inv_cancel_right]
  ring

/-- Right associativity on the kernel level. -/
theorem rightKernel_convolution (h k f : SchwartzBruhat G) :
    rightKernel μ (Hecke.TestFunction.convolution μ h k) f =
      rightKernel μ h (rightKernel μ k f) := by
  unfold rightKernel
  rw [← convolution_inversion, Hecke.TestFunction.convolution_assoc]

/-- Left associativity on the kernel level, by two compact-support Fubini swaps. -/
theorem leftKernel_convolution (h k f : SchwartzBruhat G) :
    leftKernel μ (Hecke.TestFunction.convolution μ h k) f =
      leftKernel μ k (leftKernel μ h f) := by
  ext x
  rw [leftKernel_apply, leftKernel_apply]
  simp_rw [leftKernel_apply]
  calc (∫ w, Hecke.TestFunction.convolution μ h k w * f (w * x) ∂μ)
      = ∫ w, ∫ y, h y * k (y⁻¹ * w) * f (w * x) ∂μ ∂μ := by
        congr 1
        funext w
        rw [Hecke.TestFunction.convolution_apply, ← integral_mul_const]
    _ = ∫ y, ∫ w, h y * k (y⁻¹ * w) * f (w * x) ∂μ ∂μ := by
        apply integral_integral_swap_of_hasCompactSupport
        · exact ((h.continuous.comp continuous_snd).mul
            (k.continuous.comp (continuous_snd.inv.mul continuous_fst))).mul
            (f.continuous.comp (continuous_fst.mul continuous_const))
        · apply HasCompactSupport.of_support_subset_isCompact
            (((Hecke.TestFunction.isCompact_support h).mul
              (Hecke.TestFunction.isCompact_support k)).prod
              (Hecke.TestFunction.isCompact_support h))
          rintro ⟨w, y⟩ hp
          change h y * k (y⁻¹ * w) * f (w * x) ≠ 0 at hp
          have hhk := mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hp).1
          exact ⟨⟨y, hhk.1, y⁻¹ * w, hhk.2, by simp⟩, hhk.1⟩
    _ = ∫ y, ∫ z, h y * k z * f (y * (z * x)) ∂μ ∂μ := by
        congr 1
        funext y
        rw [← integral_mul_left_eq_self (fun w => h y * k (y⁻¹ * w) * f (w * x)) y]
        simp only [inv_mul_cancel_left, mul_assoc]
    _ = ∫ z, ∫ y, h y * k z * f (y * (z * x)) ∂μ ∂μ := by
        apply integral_integral_swap_of_hasCompactSupport
        · exact ((h.continuous.comp continuous_fst).mul
            (k.continuous.comp continuous_snd)).mul
            (f.continuous.comp (continuous_fst.mul (continuous_snd.mul continuous_const)))
        · apply HasCompactSupport.of_support_subset_isCompact
            ((Hecke.TestFunction.isCompact_support h).prod
              (Hecke.TestFunction.isCompact_support k))
          rintro ⟨y, z⟩ hp
          change h y * k z * f (y * (z * x)) ≠ 0 at hp
          have hhk := mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hp).1
          exact ⟨hhk.1, hhk.2⟩
    _ = _ := by
        congr 1
        funext z
        rw [← integral_const_mul]
        congr 1
        funext y
        ring

/-- The two actions commute on the kernel level, by one compact-support Fubini swap. -/
theorem rightKernel_leftKernel (h k f : SchwartzBruhat G) :
    rightKernel μ k (leftKernel μ h f) = leftKernel μ h (rightKernel μ k f) := by
  ext x
  rw [rightKernel_apply, leftKernel_apply]
  simp_rw [rightKernel_apply, leftKernel_apply]
  calc (∫ z, k z * ∫ y, h y * f (y * (x * z)) ∂μ ∂μ)
      = ∫ z, ∫ y, k z * (h y * f (y * (x * z))) ∂μ ∂μ := by
        congr 1
        funext z
        rw [integral_const_mul]
    _ = ∫ y, ∫ z, k z * (h y * f (y * (x * z))) ∂μ ∂μ := by
        apply integral_integral_swap_of_hasCompactSupport
        · exact (k.continuous.comp continuous_fst).mul ((h.continuous.comp continuous_snd).mul
            (f.continuous.comp (continuous_snd.mul (continuous_const.mul continuous_fst))))
        · apply HasCompactSupport.of_support_subset_isCompact
            ((Hecke.TestFunction.isCompact_support k).prod
              (Hecke.TestFunction.isCompact_support h))
          rintro ⟨z, y⟩ hp
          change k z * (h y * f (y * (x * z))) ≠ 0 at hp
          have hk := mul_ne_zero_iff.mp hp
          exact ⟨hk.1, (mul_ne_zero_iff.mp hk.2).1⟩
    _ = _ := by
        congr 1
        funext y
        rw [← integral_const_mul]
        congr 1
        funext z
        rw [mul_assoc y x z]
        ring

end Kernels

section Compact

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]

/-- The right full action of a compact distribution is the original compact
convolution with the density distribution. -/
theorem rightHeckeConvolution_compact (T : compactlySupported (X := G))
    (h : Hecke.HeckeAlgebra μ) :
    rightHeckeConvolution μ (T : Distribution G) h =
      (convolution T (compactTestDensity μ (Hecke.HeckeAlgebra.toTestFunction μ h)) :
        Distribution G) := by
  ext φ
  rw [rightHeckeConvolution_eq_kernel, convolution_eq_pairing]
  symm
  apply compactSupportPairing_eq_of_agrees
  intro x _
  rw [rightKernel_apply]
  let k : LocallyConstant G ℂ := ⟨fun y => φ (x * y),
    φ.locallyConstant.comp_continuous (continuous_const.mul continuous_id)⟩
  change (∫ y, (Hecke.HeckeAlgebra.toTestFunction μ h) y * k y ∂μ) =
    compactSupportPairing (compactTestDensity μ (Hecke.HeckeAlgebra.toTestFunction μ h)) k
  exact (compactSupportPairing_testDensity μ _ k).symm

/-- The left full action of a compact distribution is the original compact
convolution with the density distribution on the left. -/
theorem leftHeckeConvolution_compact (T : compactlySupported (X := G))
    (h : Hecke.HeckeAlgebra μ) :
    leftHeckeConvolution μ h (T : Distribution G) =
      (convolution (compactTestDensity μ (Hecke.HeckeAlgebra.toTestFunction μ h)) T :
        Distribution G) := by
  ext φ
  rw [leftHeckeConvolution_eq_kernel, convolution_eq_pairing, compactPairing_swap]
  symm
  apply compactSupportPairing_eq_of_agrees
  intro y _
  rw [leftKernel_apply]
  let k : LocallyConstant G ℂ := ⟨fun x => φ (x * y),
    φ.locallyConstant.comp_continuous (continuous_id.mul continuous_const)⟩
  change (∫ x, (Hecke.HeckeAlgebra.toTestFunction μ h) x * k x ∂μ) =
    compactSupportPairing (compactTestDensity μ (Hecke.HeckeAlgebra.toTestFunction μ h)) k
  exact (compactSupportPairing_testDensity μ _ k).symm

end Compact

section Inversion

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]

omit [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] in
/-- The density identity defining an inverted Hecke element, evaluated on a test. -/
theorem integral_inversion_pair {h hi : Hecke.HeckeAlgebra μ}
    (hhi : heckeDistribution μ hi =
      GroupAction.inversionDistributions (heckeDistribution μ h))
    (ψ : SchwartzBruhat G) :
    (∫ y, (Hecke.HeckeAlgebra.toTestFunction μ h) y * ψ y⁻¹ ∂μ) =
      ∫ y, (Hecke.HeckeAlgebra.toTestFunction μ hi) y * ψ y ∂μ :=
  (LinearMap.congr_fun hhi ψ).symm

omit [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] in
/-- Both inversion laws hold for every pair related by the inverted density. -/
theorem inversion_laws (h hi : Hecke.HeckeAlgebra μ)
    (hhi : heckeDistribution μ hi =
      GroupAction.inversionDistributions (heckeDistribution μ h))
    (T : Distribution G) :
    GroupAction.inversionDistributions (rightHeckeConvolution μ T h) =
        leftHeckeConvolution μ hi (GroupAction.inversionDistributions T) ∧
      GroupAction.inversionDistributions (leftHeckeConvolution μ h T) =
        rightHeckeConvolution μ (GroupAction.inversionDistributions T) hi := by
  constructor
  · ext f
    rw [GroupAction.inversionDistributions_apply, rightHeckeConvolution_eq_kernel,
      leftHeckeConvolution_eq_kernel, GroupAction.inversionDistributions_apply]
    congr 1
    ext x
    rw [GroupAction.inversionTests_apply, rightKernel_apply, leftKernel_apply]
    have hpair := integral_inversion_pair μ hhi (Hecke.TestFunction.rightTranslate x⁻¹ f)
    simp only [Hecke.TestFunction.rightTranslate_apply] at hpair
    simp only [GroupAction.inversionTests_apply, mul_inv_rev]
    exact hpair
  · ext f
    rw [GroupAction.inversionDistributions_apply, leftHeckeConvolution_eq_kernel,
      rightHeckeConvolution_eq_kernel, GroupAction.inversionDistributions_apply]
    congr 1
    ext x
    rw [GroupAction.inversionTests_apply, leftKernel_apply, rightKernel_apply]
    have hpair := integral_inversion_pair μ hhi (Hecke.TestFunction.leftTranslate x f)
    simp only [Hecke.TestFunction.leftTranslate_apply] at hpair
    simp only [GroupAction.inversionTests_apply, mul_inv_rev]
    exact hpair

/-- Every Hecke element has an inverted Hecke element. -/
theorem exists_inverted (h : Hecke.HeckeAlgebra μ) :
    ∃ hi : Hecke.HeckeAlgebra μ, heckeDistribution μ hi =
      GroupAction.inversionDistributions (heckeDistribution μ h) := by
  obtain ⟨g, -, hg⟩ :=
    RenardUniformDensity.inversion_testDensity μ (Hecke.HeckeAlgebra.toTestFunction μ h)
  exact ⟨(Hecke.HeckeAlgebra.toTestFunction μ).symm g, hg.symm⟩

/-- Inversion preserves the actual Hecke density range. -/
theorem inversion_mem_heckeDistributionSpace {D : Distribution G}
    (hD : D ∈ heckeDistributionSpace μ) :
    GroupAction.inversionDistributions D ∈ heckeDistributionSpace μ := by
  obtain ⟨h, rfl⟩ := LinearMap.mem_range.mp hD
  obtain ⟨hi, hhi⟩ := exists_inverted μ h
  exact LinearMap.mem_range.mpr ⟨hi, hhi⟩

end Inversion

section Range

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]

/-- A left-essentially-compact distribution is carried into the Hecke density
range by every left Hecke action. -/
theorem left_mem_heckeDistributionSpace {T : Distribution G}
    (hT : T ∈ leftEssentiallyCompact μ) (h : Hecke.HeckeAlgebra μ) :
    leftHeckeConvolution μ h T ∈ heckeDistributionSpace μ := by
  classical
  have hTc : ∀ h' : Hecke.HeckeAlgebra μ,
      leftHeckeConvolution μ h' T ∈ compactlySupported := hT
  obtain ⟨K, -, hK, hKh⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance G
    {Hecke.HeckeAlgebra.toTestFunction μ h} ⊤
  have hinv := hKh _ (Finset.mem_singleton_self _)
  have hmem : leftHeckeConvolution μ h T ∈ uniformCompactDistributionsLeft (G := G) := by
    refine ⟨K, hK, ?_⟩
    rw [compactDistributionsLeft, Submodule.mem_inf]
    refine ⟨hTc h, ?_⟩
    rw [mem_fixed_iff]
    intro k
    ext f
    rw [GroupAction.leftDistributions_apply, leftHeckeConvolution_eq_kernel,
      leftHeckeConvolution_eq_kernel]
    congr 1
    ext x
    rw [leftKernel_apply, leftKernel_apply]
    simp only [GroupAction.leftTests_apply, inv_inv]
    rw [← integral_mul_left_eq_self
      (fun y => (Hecke.HeckeAlgebra.toTestFunction μ h) y * f (y * x)) (k : G)]
    congr 1
    funext y
    rw [hinv.1 k y, mul_assoc]
  have hrange := (RenardUniformDensity.uniformRange G μ).2.1
  have hmem' : leftHeckeConvolution μ h T ∈
      (LinearMap.range (testDensity μ) : Set (Distribution G)) := by
    rw [hrange]
    exact hmem
  obtain ⟨g, hg⟩ := LinearMap.mem_range.mp hmem'
  exact LinearMap.mem_range.mpr ⟨(Hecke.HeckeAlgebra.toTestFunction μ).symm g, hg⟩

/-- The right case follows from the left case through the inversion laws. -/
theorem right_mem_heckeDistributionSpace {T : Distribution G}
    (hT : T ∈ rightEssentiallyCompact μ) (h : Hecke.HeckeAlgebra μ) :
    rightHeckeConvolution μ T h ∈ heckeDistributionSpace μ := by
  have hTc : ∀ h' : Hecke.HeckeAlgebra μ,
      rightHeckeConvolution μ T h' ∈ compactlySupported := hT
  have hTinv : GroupAction.inversionDistributions T ∈ leftEssentiallyCompact μ := by
    show ∀ h' : Hecke.HeckeAlgebra μ,
      leftHeckeConvolution μ h' (GroupAction.inversionDistributions T) ∈ compactlySupported
    intro h'
    obtain ⟨h'', hh''⟩ := exists_inverted μ h'
    have hback : heckeDistribution μ h' =
        GroupAction.inversionDistributions (heckeDistribution μ h'') := by
      rw [hh'', GroupAction.inversionDistributions_inversionDistributions]
    rw [← (inversion_laws μ h'' h' hback T).1]
    exact RenardUniformDensity.inversion_mem_compactlySupported (hTc h'')
  obtain ⟨hi, hhi⟩ := exists_inverted μ h
  have hleft := left_mem_heckeDistributionSpace μ hTinv hi
  rw [← (inversion_laws μ h hi hhi T).1] at hleft
  have hfinal := inversion_mem_heckeDistributionSpace μ hleft
  rwa [GroupAction.inversionDistributions_inversionDistributions] at hfinal

end Range

theorem kernel : KernelStatement.{uG} := by
  intro G _ _ _ _ _ _ _ _ μ _ h f
  refine ⟨fun x => ⟨?_, ?_⟩,
    rightKernel μ (Hecke.HeckeAlgebra.toTestFunction μ h) f,
    leftKernel μ (Hecke.HeckeAlgebra.toTestFunction μ h) f,
    rightKernel_apply μ _ f, leftKernel_apply μ _ f, fun T => ⟨rfl, rfl⟩⟩
  · exact ((Hecke.HeckeAlgebra.toTestFunction μ h).continuous.mul
      (f.continuous.comp (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport
      (Hecke.HeckeAlgebra.toTestFunction μ h).hasCompactSupport.mul_right
  · exact ((Hecke.HeckeAlgebra.toTestFunction μ h).continuous.mul
      (f.continuous.comp (continuous_id.mul continuous_const))).integrable_of_hasCompactSupport
      (Hecke.HeckeAlgebra.toTestFunction μ h).hasCompactSupport.mul_right

theorem compactCompatibility : CompactCompatibilityStatement.{uG} := by
  intro G _ _ _ _ _ _ _ _ μ _ T h
  exact ⟨compactTestDensity μ (Hecke.HeckeAlgebra.toTestFunction μ h), rfl,
    rightHeckeConvolution_compact μ T h, leftHeckeConvolution_compact μ T h⟩

theorem inversionLaws : InversionStatement.{uG} := by
  intro G _ _ _ _ _ _ _ _ μ _ h
  obtain ⟨hi, hhi⟩ := exists_inverted μ h
  exact ⟨hi, hhi, inversion_laws μ h hi hhi⟩

theorem associativity : AssociativityStatement.{uG} := by
  intro G _ _ _ _ _ _ _ _ μ _ T h k
  refine ⟨?_, ?_, ?_⟩
  · ext f
    rw [rightHeckeConvolution_eq_kernel, rightHeckeConvolution_eq_kernel,
      rightHeckeConvolution_eq_kernel]
    exact congrArg T (rightKernel_convolution μ _ _ f)
  · ext f
    rw [leftHeckeConvolution_eq_kernel, leftHeckeConvolution_eq_kernel,
      leftHeckeConvolution_eq_kernel]
    exact congrArg T (leftKernel_convolution μ _ _ f)
  · ext f
    rw [leftHeckeConvolution_eq_kernel, rightHeckeConvolution_eq_kernel,
      rightHeckeConvolution_eq_kernel, leftHeckeConvolution_eq_kernel]
    exact congrArg T (rightKernel_leftKernel μ _ _ f)

theorem evaluation : EvaluationStatement.{uG} := by
  intro G _ _ _ _ _ _ _ _ μ _ T h f
  rw [rightHeckeConvolution_eq_kernel]
  unfold leftConvolveTest
  rw [Hecke.TestFunction.leftTranslate_one]
  congr 1
  have hc := convolution_inversion μ (Hecke.TestFunction.inversion f)
    (Hecke.HeckeAlgebra.toTestFunction μ h)
  rw [Hecke.TestFunction.inversion_inversion] at hc
  exact hc

theorem inclusions : InclusionsStatement.{uG} := by
  intro G _ _ _ _ _ _ _ _ μ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro D hD
    obtain ⟨h, rfl⟩ := LinearMap.mem_range.mp hD
    exact (compactTestDensity μ (Hecke.HeckeAlgebra.toTestFunction μ h)).property
  · intro T hT
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · show ∀ h : Hecke.HeckeAlgebra μ, rightHeckeConvolution μ T h ∈ compactlySupported
      intro h
      have hc := rightHeckeConvolution_compact μ ⟨T, hT⟩ h
      change rightHeckeConvolution μ T h = _ at hc
      rw [hc]
      exact (convolution _ _).property
    · show ∀ h : Hecke.HeckeAlgebra μ, leftHeckeConvolution μ h T ∈ compactlySupported
      intro h
      have hc := leftHeckeConvolution_compact μ ⟨T, hT⟩ h
      change leftHeckeConvolution μ h T = _ at hc
      rw [hc]
      exact (convolution _ _).property
  · exact inf_le_left
  · exact inf_le_right

theorem rangePreservation : RangePreservationStatement.{uG} := by
  intro G _ _ _ _ _ _ _ _ μ _
  exact ⟨fun T h => right_mem_heckeDistributionSpace μ T.property h,
    fun T h => left_mem_heckeDistributionSpace μ T.property h⟩

/-- Renard II.3.13: all seven published full-distribution Hecke assertions. -/
theorem statements : Statements.{uG} :=
  ⟨kernel, compactCompatibility, inversionLaws, associativity, evaluation, inclusions,
    rangePreservation⟩

end Langlands.HarmonicAnalysis.Distribution.RenardFullHecke

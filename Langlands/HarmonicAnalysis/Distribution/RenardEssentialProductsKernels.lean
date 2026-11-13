import Langlands.HarmonicAnalysis.Distribution.RenardEssentialProductsStatements
import Langlands.HarmonicAnalysis.Distribution.RenardConvolutionProof
import Langlands.HarmonicAnalysis.Distribution.RenardModularProof
import Langlands.Topology.LocallyProfiniteProof
import Langlands.Representation.Hecke.CommonInvarianceProof
import Langlands.HarmonicAnalysis.Distribution.RenardUniformDensityProof
import Langlands.HarmonicAnalysis.Distribution.RenardCompactSubgroupProof

/-! # Kernels of the full Hecke actions on algebraic distributions -/

set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory
open scoped Pointwise

namespace Langlands.HarmonicAnalysis.Distribution.RenardEssentialProducts

universe uG

section Kernels

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]

/-- The scalar function `x ↦ U(y ↦ f(x*y))`. -/
def rightKernel (U : Distribution G) (f : SchwartzBruhat G) (x : G) : ℂ :=
  U (Hecke.TestFunction.leftTranslate x⁻¹ f)

/-- The scalar function `y ↦ T(x ↦ f(x*y))`. -/
def leftKernel (T : Distribution G) (f : SchwartzBruhat G) (y : G) : ℂ :=
  T (Hecke.TestFunction.rightTranslate y f)

@[simp] theorem leftTranslate_inv_apply (x y : G) (f : SchwartzBruhat G) :
    Hecke.TestFunction.leftTranslate x⁻¹ f y = f (x * y) := by
  simp [Hecke.TestFunction.leftTranslate_apply]

theorem rightKernel_locallyConstant (U : Distribution G) (f : SchwartzBruhat G) :
    IsLocallyConstant (rightKernel U f) := by
  have he : rightKernel U f =
      fun x => leftConvolveTest U (Hecke.TestFunction.inversion f) x⁻¹ := by
    funext x
    unfold rightKernel leftConvolveTest
    rw [Hecke.TestFunction.inversion_inversion]
  rw [he]
  exact (leftConvolveTest_locallyConstant U _).comp_continuous continuous_inv

theorem leftKernel_locallyConstant (T : Distribution G) (f : SchwartzBruhat G) :
    IsLocallyConstant (leftKernel T f) := by
  have he : leftKernel T f =
      fun y => rightConvolveTest (Hecke.TestFunction.inversion f) T y⁻¹ := by
    funext y
    unfold leftKernel rightConvolveTest
    rw [Hecke.TestFunction.inversion_inversion, inv_inv]
  rw [he]
  exact (rightConvolveTest_locallyConstant T _).comp_continuous continuous_inv

theorem rightKernel_linear (U : Distribution G) (f g : SchwartzBruhat G) (c : ℂ) :
    rightKernel U (f + c • g) = rightKernel U f + c • rightKernel U g := by
  funext x
  simp [rightKernel, map_add, map_smul]

theorem leftKernel_linear (T : Distribution G) (f g : SchwartzBruhat G) (c : ℂ) :
    leftKernel T (f + c • g) = leftKernel T f + c • leftKernel T g := by
  funext x
  simp [leftKernel, map_add, map_smul]

/-- Pointwise vanishing outside a compact set gives compact support. -/
theorem hasCompactSupport_of_vanishing {φ : G → ℂ} {S : Set G} (hS : IsCompact S)
    (hφ : ∀ x, x ∉ S → φ x = 0) : HasCompactSupport φ :=
  HasCompactSupport.of_support_subset_isCompact hS (fun x hx => by
    by_contra h
    exact hx (hφ x h))

theorem leftKernel_apply (T : Distribution G) (f : SchwartzBruhat G) (y : G) :
    leftKernel T f y = T (Hecke.TestFunction.rightTranslate y f) := rfl

theorem rightKernel_apply (U : Distribution G) (f : SchwartzBruhat G) (x : G) :
    rightKernel U f x = U (Hecke.TestFunction.leftTranslate x⁻¹ f) := rfl

/-- The normalized compact-subgroup integral computes right convolution with `e_K`. -/
theorem rightConvolveTest_compactSubgroupHaar (K : Subgroup G) (hK : IsCompact (K : Set G))
    (f : SchwartzBruhat G) (x : G) :
    rightConvolveTest f (compactSubgroupHaar K hK : Distribution G) x =
      subgroupIntegral K hK (fun k => f (x * k⁻¹)) := by
  unfold rightConvolveTest
  change subgroupIntegral K hK _ = _
  apply subgroupIntegral_congr
  intro k _
  simp

/-- The normalized compact-subgroup integral computes left convolution with `e_K`. -/
theorem leftConvolveTest_compactSubgroupHaar (K : Subgroup G) (hK : IsCompact (K : Set G))
    (f : SchwartzBruhat G) (x : G) :
    leftConvolveTest (compactSubgroupHaar K hK : Distribution G) f x =
      subgroupIntegral K hK (fun k => f (k⁻¹ * x)) := by
  unfold leftConvolveTest
  change subgroupIntegral K hK _ = _
  apply subgroupIntegral_congr
  intro k _
  simp

/-- `f * e_K = f` exactly when `f` is right `K`-invariant. -/
theorem rightConvolveTest_eq_iff (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (f : SchwartzBruhat G) :
    rightConvolveTest f (compactSubgroupHaar K.toSubgroup hK : Distribution G) =
        (f : G → ℂ) ↔ ∀ k ∈ K, ∀ x, f (x * k) = f x := by
  constructor
  · intro hf k hk x
    have h1 := congrFun hf (x * k)
    have h2 := congrFun hf x
    rw [rightConvolveTest_compactSubgroupHaar] at h1 h2
    rw [← h1, ← h2]
    have hm := subgroupIntegral_mul_right K.toSubgroup hK (fun k' => f (x * k'⁻¹))
      (K.toSubgroup.inv_mem hk)
    rw [← hm]
    apply subgroupIntegral_congr
    intro y _
    simp [mul_assoc]
  · intro hf
    funext x
    rw [rightConvolveTest_compactSubgroupHaar,
      subgroupIntegral_congr K.toSubgroup hK (ψ := fun _ => f x)
        (fun k hk => hf k⁻¹ (K.toSubgroup.inv_mem hk) x)]
    exact subgroupIntegral_const _ _ _

/-- `e_K * f = f` exactly when `f` is left `K`-invariant. -/
theorem leftConvolveTest_eq_iff (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (f : SchwartzBruhat G) :
    leftConvolveTest (compactSubgroupHaar K.toSubgroup hK : Distribution G) f =
        (f : G → ℂ) ↔ ∀ k ∈ K, ∀ x, f (k * x) = f x := by
  constructor
  · intro hf k hk x
    have h1 := congrFun hf (k * x)
    have h2 := congrFun hf x
    rw [leftConvolveTest_compactSubgroupHaar] at h1 h2
    rw [← h1, ← h2]
    have hm := subgroupIntegral_mul_left K.toSubgroup hK (fun k' => f (k'⁻¹ * x))
      (K.toSubgroup.inv_mem hk)
    rw [← hm]
    apply subgroupIntegral_congr
    intro y _
    simp [mul_assoc]
  · intro hf
    funext x
    rw [leftConvolveTest_compactSubgroupHaar,
      subgroupIntegral_congr K.toSubgroup hK (ψ := fun _ => f x)
        (fun k hk => hf k⁻¹ (K.toSubgroup.inv_mem hk) x)]
    exact subgroupIntegral_const _ _ _

/-- Every test is right invariant under some compact open subgroup. -/
theorem exists_biInvariant (f : SchwartzBruhat G) :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧
      (∀ k ∈ K, ∀ x, f (k * x) = f x) ∧ ∀ k ∈ K, ∀ x, f (x * k) = f x := by
  classical
  obtain ⟨K, -, hK, hKf⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance G {f} ⊤
  have hf := hKf f (by simp)
  exact ⟨K, hK, fun k hk x => hf.1 ⟨k, hk⟩ x, fun k hk x => hf.2 ⟨k, hk⟩ x⟩

/-- Compact convolution evaluated through the right kernel of its second factor. -/
theorem convolution_apply_rightKernel (T U : compactlySupported (X := G))
    (f g : SchwartzBruhat G) (hg : ∀ x, g x = rightKernel (U : Distribution G) f x) :
    (convolution T U : Distribution G) f = (T : Distribution G) g := by
  rw [convolution_eq_pairing, ← compactSupportPairing_testFunction T g]
  congr 1
  ext x
  rw [compactPartial_apply]
  change _ = g x
  rw [hg x, rightKernel_apply]
  apply compactSupportPairing_eq_of_agrees
  intro y _
  simp [mulFunction]

/-- Compact convolution evaluated through the left kernel of its first factor. -/
theorem convolution_apply_leftKernel (T U : compactlySupported (X := G))
    (f g : SchwartzBruhat G) (hg : ∀ y, g y = leftKernel (T : Distribution G) f y) :
    (convolution T U : Distribution G) f = (U : Distribution G) g := by
  rw [convolution_eq_pairing, compactPairing_swap, ← compactSupportPairing_testFunction U g]
  congr 1
  ext y
  rw [compactPartial_apply]
  change _ = g y
  rw [hg y, leftKernel_apply]
  apply compactSupportPairing_eq_of_agrees
  intro x _
  simp [mulFunction]

end Kernels

section Measure

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]

/-- Integration against the inverse measure. -/
theorem integral_inv_measure (g : G → ℂ) : (∫ y, g y ∂μ.inv) = ∫ y, g y⁻¹ ∂μ := by
  rw [Measure.inv_def]
  exact integral_map_equiv (MeasurableEquiv.inv G) g

/-- The right Hecke kernel: `(f ⋆ ȟ)(x) = ∫ h(y) f(xy) dμ(y)`. -/
theorem convolution_inversion_apply (f h : SchwartzBruhat G) (x : G) :
    Hecke.TestFunction.convolution μ f (Hecke.TestFunction.inversion h) x =
      ∫ y, h y * f (x * y) ∂μ := by
  rw [Hecke.TestFunction.convolution_apply,
    ← integral_mul_left_eq_self (μ := μ)
      (fun y => f y * Hecke.TestFunction.inversion h (y⁻¹ * x)) x]
  congr 1
  funext y
  simp only [Hecke.TestFunction.inversion_apply, mul_inv_rev, inv_mul_cancel_right, inv_inv]
  ring

/-- The left Hecke kernel: `(ȟ ⋆_{μ⁻¹} f)(x) = ∫ h(y) f(yx) dμ(y)`. -/
theorem convolution_inv_inversion_apply (h f : SchwartzBruhat G) (x : G) :
    Hecke.TestFunction.convolution μ.inv (Hecke.TestFunction.inversion h) f x =
      ∫ y, h y * f (y * x) ∂μ := by
  rw [Hecke.TestFunction.convolution_apply, integral_inv_measure]
  simp only [Hecke.TestFunction.inversion_apply, inv_inv]

theorem rightKernel_testDensity (h f : SchwartzBruhat G) :
    rightKernel (testDensity μ h) f =
      ⇑(Hecke.TestFunction.convolution μ f (Hecke.TestFunction.inversion h)) := by
  funext x
  rw [convolution_inversion_apply]
  simp [rightKernel, testDensity_apply]

theorem leftKernel_testDensity (h f : SchwartzBruhat G) :
    leftKernel (testDensity μ h) f =
      ⇑(Hecke.TestFunction.convolution μ.inv (Hecke.TestFunction.inversion h) f) := by
  funext y
  rw [convolution_inv_inversion_apply]
  simp [leftKernel, testDensity_apply]

/-- Evaluation of the right Hecke action through the left kernel (Fubini). -/
theorem rightHecke_eval (T : Distribution G) (h f : SchwartzBruhat G) :
    T (Hecke.TestFunction.convolution μ f (Hecke.TestFunction.inversion h)) =
      ∫ y, h y * leftKernel T f y ∂μ := by
  have he : Hecke.TestFunction.convolution μ f (Hecke.TestFunction.inversion h) =
      SchwartzBruhat.partialIntegral (leftDensityKernel h f) μ := by
    ext x
    rw [convolution_inversion_apply]
    rfl
  rw [he, distribution_partialIntegral]
  congr 1
  funext y
  have hs : SchwartzBruhat.sliceFst (leftDensityKernel h f) y =
      h y • Hecke.TestFunction.rightTranslate y f := by
    ext x
    simp [leftDensityKernel]
  rw [hs, map_smul, smul_eq_mul]
  rfl

/-- Evaluation of the left Hecke action through the right kernel (Fubini). -/
theorem leftHecke_eval (T : Distribution G) (h f : SchwartzBruhat G) :
    T (Hecke.TestFunction.convolution μ.inv (Hecke.TestFunction.inversion h) f) =
      ∫ x, h x * rightKernel T f x ∂μ := by
  have he : Hecke.TestFunction.convolution μ.inv (Hecke.TestFunction.inversion h) f =
      SchwartzBruhat.partialIntegral (rightDensityKernel h f) μ := by
    ext y
    rw [convolution_inv_inversion_apply]
    rfl
  rw [he, distribution_partialIntegral]
  congr 1
  funext x
  have hs : SchwartzBruhat.sliceFst (rightDensityKernel h f) x =
      h x • Hecke.TestFunction.leftTranslate x⁻¹ f := by
    ext y
    simp [rightDensityKernel]
  rw [hs, map_smul, smul_eq_mul]
  rfl

/-- The right Hecke action of an arbitrary distribution is a locally constant density. -/
theorem rightHeckeConvolution_eq_density (U : Distribution G) (h : Hecke.HeckeAlgebra μ) :
    rightHeckeConvolution μ U h =
      density μ ⟨leftConvolveTest U (Hecke.HeckeAlgebra.toTestFunction μ h),
        leftConvolveTest_locallyConstant _ _⟩ := by
  ext f
  rw [rightHeckeConvolution_apply, density_apply]
  set h' := Hecke.HeckeAlgebra.toTestFunction μ h
  have he : Hecke.TestFunction.convolution μ f (Hecke.TestFunction.inversion h') =
      SchwartzBruhat.partialIntegral (leftDensityChangedKernel h' f) μ := by
    ext x
    rw [Hecke.TestFunction.convolution_apply, SchwartzBruhat.partialIntegral_apply]
    congr 1
    funext y
    simp [leftDensityChangedKernel, mul_comm]
  rw [he, distribution_partialIntegral]
  congr 1
  funext z
  have hs : SchwartzBruhat.sliceFst (leftDensityChangedKernel h' f) z =
      f z • Hecke.TestFunction.leftTranslate z (Hecke.TestFunction.inversion h') := by
    ext x
    simp [leftDensityChangedKernel, mul_comm]
  rw [hs, map_smul, smul_eq_mul]
  change f z * leftConvolveTest U h' z = leftConvolveTest U h' z * f z
  exact mul_comm _ _

theorem normalizedIndicator_test_apply (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (y : G) :
    Hecke.HeckeAlgebra.toTestFunction μ (Hecke.HeckeAlgebra.normalizedIndicator μ K hK) y =
      (μ.real (K : Set G) : ℂ)⁻¹ * (K : Set G).indicator (fun _ => (1 : ℂ)) y := rfl

/-- Averaging a function constant on `K` against the normalized indicator. -/
theorem integral_normalizedIndicator_mul (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (φ : G → ℂ) (c : ℂ) (hφ : ∀ y ∈ K, φ y = c) :
    (∫ y, Hecke.HeckeAlgebra.toTestFunction μ
        (Hecke.HeckeAlgebra.normalizedIndicator μ K hK) y * φ y ∂μ) = c := by
  have hpt : ∀ y, Hecke.HeckeAlgebra.toTestFunction μ
      (Hecke.HeckeAlgebra.normalizedIndicator μ K hK) y * φ y =
      (μ.real (K : Set G) : ℂ)⁻¹ * (K : Set G).indicator (fun _ => c) y := by
    intro y
    rw [normalizedIndicator_test_apply]
    by_cases hy : y ∈ (K : Set G)
    · simp [hy, hφ y hy]
    · simp [hy]
  simp_rw [hpt]
  rw [integral_const_mul, integral_indicator_const _ K.isOpen.measurableSet,
    Complex.real_smul, ← mul_assoc,
    inv_mul_cancel₀ (Hecke.HeckeAlgebra.compactOpen_complex_mass_ne_zero μ K hK), one_mul]

/-- Right convolution with the normalized indicator fixes right `K`-invariant tests. -/
theorem convolution_normalizedIndicator_of_right (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (g : SchwartzBruhat G) (hg : ∀ k ∈ K, ∀ x, g (x * k) = g x) :
    Hecke.TestFunction.convolution μ g (Hecke.TestFunction.inversion
      (Hecke.HeckeAlgebra.toTestFunction μ (Hecke.HeckeAlgebra.normalizedIndicator μ K hK))) =
      g := by
  ext x
  rw [convolution_inversion_apply]
  exact integral_normalizedIndicator_mul μ K hK _ (g x) (fun y hy => hg y hy x)

/-- Left convolution with the normalized indicator fixes left `K`-invariant tests. -/
theorem convolution_normalizedIndicator_of_left (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (g : SchwartzBruhat G) (hg : ∀ k ∈ K, ∀ x, g (k * x) = g x) :
    Hecke.TestFunction.convolution μ.inv (Hecke.TestFunction.inversion
      (Hecke.HeckeAlgebra.toTestFunction μ (Hecke.HeckeAlgebra.normalizedIndicator μ K hK)))
      g = g := by
  ext x
  rw [convolution_inv_inversion_apply]
  exact integral_normalizedIndicator_mul μ K hK _ (g x) (fun y hy => hg y hy x)

/-- For right `K`-invariant `f`, the right kernel does not see `U * e_K` versus `U`. -/
theorem rightKernel_rightHecke_normalizedIndicator (U : Distribution G) (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (f : SchwartzBruhat G) (hf : ∀ k ∈ K, ∀ x, f (x * k) = f x) :
    rightKernel (rightHeckeConvolution μ U (Hecke.HeckeAlgebra.normalizedIndicator μ K hK)) f =
      rightKernel U f := by
  funext x
  rw [rightKernel_apply, rightKernel_apply, rightHeckeConvolution_apply,
    convolution_normalizedIndicator_of_right]
  intro k hk y
  simp only [leftTranslate_inv_apply, ← mul_assoc, hf k hk]

/-- For left `K`-invariant `f`, the left kernel does not see `e_K * T` versus `T`. -/
theorem leftKernel_leftHecke_normalizedIndicator (T : Distribution G) (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (f : SchwartzBruhat G) (hf : ∀ k ∈ K, ∀ x, f (k * x) = f x) :
    leftKernel (leftHeckeConvolution μ (Hecke.HeckeAlgebra.normalizedIndicator μ K hK) T) f =
      leftKernel T f := by
  funext y
  rw [leftKernel_apply, leftKernel_apply, leftHeckeConvolution_apply,
    convolution_normalizedIndicator_of_left]
  intro k hk x
  simp only [Hecke.TestFunction.rightTranslate_apply, mul_assoc, hf k hk]

/-- Left translation commutes with right Hecke convolution. -/
theorem leftTranslate_convolution_inversion (x : G) (f h : SchwartzBruhat G) :
    Hecke.TestFunction.leftTranslate x⁻¹
        (Hecke.TestFunction.convolution μ f (Hecke.TestFunction.inversion h)) =
      Hecke.TestFunction.convolution μ (Hecke.TestFunction.leftTranslate x⁻¹ f)
        (Hecke.TestFunction.inversion h) := by
  ext z
  rw [leftTranslate_inv_apply, convolution_inversion_apply, convolution_inversion_apply]
  simp only [leftTranslate_inv_apply, mul_assoc]

/-- Right translation commutes with left Hecke convolution. -/
theorem rightTranslate_convolution_inv_inversion (y : G) (h f : SchwartzBruhat G) :
    Hecke.TestFunction.rightTranslate y
        (Hecke.TestFunction.convolution μ.inv (Hecke.TestFunction.inversion h) f) =
      Hecke.TestFunction.convolution μ.inv (Hecke.TestFunction.inversion h)
        (Hecke.TestFunction.rightTranslate y f) := by
  ext z
  rw [Hecke.TestFunction.rightTranslate_apply, convolution_inv_inversion_apply,
    convolution_inv_inversion_apply]
  simp only [Hecke.TestFunction.rightTranslate_apply, mul_assoc]

/-- A right-essentially-compact distribution has test densities as right Hecke products. -/
theorem exists_testDensity_eq_right {U : Distribution G}
    (hU : U ∈ rightEssentiallyCompact μ) (h : Hecke.HeckeAlgebra μ) :
    ∃ k : SchwartzBruhat G, testDensity μ k = rightHeckeConvolution μ U h := by
  have hc := hU h
  rw [rightHeckeConvolution_eq_density] at hc ⊢
  set ψ : LocallyConstant G ℂ := ⟨leftConvolveTest U (Hecke.HeckeAlgebra.toTestFunction μ h),
    leftConvolveTest_locallyConstant _ _⟩
  have hcomp : IsCompact (Function.support (ψ : G → ℂ)) := by
    rw [← RenardHaar.density_support μ ψ]
    exact (mem_compactlySupported_iff _).mp hc
  exact ⟨⟨(ψ : G → ℂ), ψ.isLocallyConstant,
    HasCompactSupport.of_support_subset_isCompact hcomp subset_rfl⟩, rfl⟩

/-- A left-essentially-compact distribution has test densities as left Hecke products. -/
theorem exists_testDensity_eq_left {T : Distribution G}
    (hT : T ∈ leftEssentiallyCompact μ) (h : Hecke.HeckeAlgebra μ) :
    ∃ k : SchwartzBruhat G, testDensity μ k = leftHeckeConvolution μ h T := by
  obtain ⟨K, hK, hl, -⟩ := exists_biInvariant (Hecke.HeckeAlgebra.toTestFunction μ h)
  have hmem : leftHeckeConvolution μ h T ∈
      (GroupFunctionSpaces.uniformCompactDistributionsLeft : Set (Distribution G)) := by
    refine ⟨K, hK, ?_⟩
    rw [GroupFunctionSpaces.compactDistributionsLeft, Submodule.mem_inf]
    refine ⟨hT h, ?_⟩
    rw [GroupFunctionSpaces.mem_fixed_iff]
    intro k
    ext f
    change T (Hecke.TestFunction.convolution μ.inv (Hecke.TestFunction.inversion
        (Hecke.HeckeAlgebra.toTestFunction μ h)) (GroupAction.leftTests (k : G)⁻¹ f)) =
      T (Hecke.TestFunction.convolution μ.inv (Hecke.TestFunction.inversion
        (Hecke.HeckeAlgebra.toTestFunction μ h)) f)
    congr 1
    ext x
    rw [convolution_inv_inversion_apply, convolution_inv_inversion_apply,
      ← integral_mul_left_eq_self (μ := μ)
        (fun y => Hecke.HeckeAlgebra.toTestFunction μ h y * f (y * x)) (k : G)]
    congr 1
    funext y
    simp only [GroupAction.leftTests_apply, inv_inv, hl (k : G) k.property y, mul_assoc]
  obtain ⟨g, hg⟩ := LinearMap.mem_range.mp (RenardUniformDensity.left_subset_range μ hmem)
  exact ⟨g, hg⟩

/-- Right Hecke products of compact distributions are compact convolutions. -/
theorem convolution_compactTestDensity_apply (T : compactlySupported (X := G))
    (h f : SchwartzBruhat G) :
    (convolution T (compactTestDensity μ h) : Distribution G) f =
      (T : Distribution G)
        (Hecke.TestFunction.convolution μ f (Hecke.TestFunction.inversion h)) := by
  apply convolution_apply_rightKernel
  intro x
  change _ = rightKernel (testDensity μ h) f x
  rw [rightKernel_testDensity]

/-- Left Hecke products of compact distributions are compact convolutions. -/
theorem compactTestDensity_convolution_apply (T : compactlySupported (X := G))
    (h f : SchwartzBruhat G) :
    (convolution (compactTestDensity μ h) T : Distribution G) f =
      (T : Distribution G)
        (Hecke.TestFunction.convolution μ.inv (Hecke.TestFunction.inversion h) f) := by
  apply convolution_apply_leftKernel
  intro y
  rw [convolution_inv_inversion_apply]
  rfl

theorem compactlySupported_le_right :
    compactlySupported (X := G) ≤ rightEssentiallyCompact μ := by
  intro T hT h
  have he : rightHeckeConvolution μ T h = (convolution ⟨T, hT⟩
      (compactTestDensity μ (Hecke.HeckeAlgebra.toTestFunction μ h)) : Distribution G) := by
    ext f
    rw [convolution_compactTestDensity_apply]
    rfl
  rw [he]
  exact Subtype.property _

theorem compactlySupported_le_left :
    compactlySupported (X := G) ≤ leftEssentiallyCompact μ := by
  intro T hT h
  have he : leftHeckeConvolution μ h T = (convolution
      (compactTestDensity μ (Hecke.HeckeAlgebra.toTestFunction μ h)) ⟨T, hT⟩ :
        Distribution G) := by
    ext f
    rw [compactTestDensity_convolution_apply]
    rfl
  rw [he]
  exact Subtype.property _

end Measure

end Langlands.HarmonicAnalysis.Distribution.RenardEssentialProducts

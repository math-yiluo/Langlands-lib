import Langlands.HarmonicAnalysis.Distribution.RenardCompletionStatements
import Langlands.HarmonicAnalysis.Distribution.RenardConvolutionProof
import Langlands.HarmonicAnalysis.Distribution.RenardHaarDensityProof

/-! # Renard II.3.13: laws of the full Hecke actions on algebraic distributions -/

noncomputable section

open MeasureTheory

namespace Langlands.HarmonicAnalysis.Distribution.RenardCompletion

universe uG

section Laws

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]

/-- The test `f * ȟ` occurring in the transpose `T*h`, in right-translated form. -/
theorem convolution_inversion_apply (f h : SchwartzBruhat G) (x : G) :
    Hecke.TestFunction.convolution μ f (Hecke.TestFunction.inversion h) x =
      ∫ y, f (x * y) * h y ∂μ := by
  rw [Hecke.TestFunction.convolution_apply,
    ← integral_mul_left_eq_self (fun y => f y * Hecke.TestFunction.inversion h (y⁻¹ * x)) x]
  congr 1
  funext y
  simp only [Hecke.TestFunction.inversion_apply, mul_inv_rev, inv_inv, inv_mul_cancel_left]

/-- Bare inversion reverses left-Haar convolution of test functions. -/
theorem inversion_convolution (h k : SchwartzBruhat G) :
    Hecke.TestFunction.inversion (Hecke.TestFunction.convolution μ h k) =
      Hecke.TestFunction.convolution μ (Hecke.TestFunction.inversion k)
        (Hecke.TestFunction.inversion h) := by
  ext x
  rw [Hecke.TestFunction.inversion_apply, Hecke.TestFunction.convolution_apply,
    Hecke.TestFunction.convolution_apply,
    ← integral_mul_left_eq_self (fun y => Hecke.TestFunction.inversion k y *
      Hecke.TestFunction.inversion h (y⁻¹ * x)) x]
  congr 1
  funext y
  simp only [Hecke.TestFunction.inversion_apply]
  rw [show ((x * y)⁻¹ * x)⁻¹ = y by group, show (x * y)⁻¹ = y⁻¹ * x⁻¹ by group]
  exact mul_comm (h y) (k (y⁻¹ * x⁻¹))

/-- The test operator of the right action is associative in the Hecke variable. -/
theorem rightTest_assoc (f h k : SchwartzBruhat G) :
    Hecke.TestFunction.convolution μ (Hecke.TestFunction.convolution μ f
        (Hecke.TestFunction.inversion k)) (Hecke.TestFunction.inversion h) =
      Hecke.TestFunction.convolution μ f (Hecke.TestFunction.inversion
        (Hecke.TestFunction.convolution μ h k)) := by
  rw [Hecke.TestFunction.convolution_assoc, inversion_convolution]

/-- Right associativity of the full right Hecke action: `(T*h)*k = T*(h*k)`. -/
theorem rightHeckeConvolution_mul (T : Distribution G) (h k : Hecke.HeckeAlgebra μ) :
    rightHeckeConvolution μ (rightHeckeConvolution μ T h) k =
      rightHeckeConvolution μ T (h * k) := by
  ext f
  exact congrArg T (rightTest_assoc μ f (Hecke.HeckeAlgebra.toTestFunction μ h)
    (Hecke.HeckeAlgebra.toTestFunction μ k))

/-- Integration against a Hecke density is a convolution evaluated at `1`. -/
theorem heckeDistribution_apply_eq_convolution (k : Hecke.HeckeAlgebra μ)
    (φ : SchwartzBruhat G) :
    heckeDistribution μ k φ =
      Hecke.TestFunction.convolution μ (Hecke.HeckeAlgebra.toTestFunction μ k)
        (Hecke.TestFunction.inversion φ) 1 := by
  rw [heckeDistribution_apply, Hecke.TestFunction.convolution_apply]
  congr 1
  funext y
  simp only [Hecke.TestFunction.inversion_apply, mul_one, inv_inv]
  rfl

/-- The full right action on a Hecke density is the Hecke product. -/
theorem rightHeckeConvolution_heckeDistribution (k h : Hecke.HeckeAlgebra μ) :
    rightHeckeConvolution μ (heckeDistribution μ k) h = heckeDistribution μ (k * h) := by
  ext f
  rw [rightHeckeConvolution_apply, heckeDistribution_apply_eq_convolution,
    heckeDistribution_apply_eq_convolution, inversion_convolution,
    Hecke.TestFunction.inversion_inversion]
  exact (congrArg (fun φ : SchwartzBruhat G => φ 1) (Hecke.TestFunction.convolution_assoc μ
    (Hecke.HeckeAlgebra.toTestFunction μ k) (Hecke.HeckeAlgebra.toTestFunction μ h)
    (Hecke.TestFunction.inversion f))).symm

omit [μ.IsHaarMeasure] in
/-- The test `ȟ * f` (for `μ.inv`) occurring in the transpose `h*T`. -/
theorem convolution_inv_apply (h f : SchwartzBruhat G) (x : G) :
    Hecke.TestFunction.convolution μ.inv (Hecke.TestFunction.inversion h) f x =
      ∫ y, h y * f (y * x) ∂μ := by
  rw [Hecke.TestFunction.convolution_apply]
  have hm : MeasurableEmbedding (fun y : G => y⁻¹) :=
    (MeasurableEquiv.inv G).measurableEmbedding
  change (∫ y, Hecke.TestFunction.inversion h y * f (y⁻¹ * x)
    ∂(Measure.map (fun y : G => y⁻¹) μ)) = _
  rw [hm.integral_map]
  simp only [Hecke.TestFunction.inversion_apply, inv_inv]

/-- The full left action on a Hecke density is the Hecke product. -/
theorem leftHeckeConvolution_heckeDistribution (h k : Hecke.HeckeAlgebra μ) :
    leftHeckeConvolution μ h (heckeDistribution μ k) = heckeDistribution μ (h * k) := by
  ext f
  let h' : SchwartzBruhat G := Hecke.HeckeAlgebra.toTestFunction μ h
  let k' : SchwartzBruhat G := Hecke.HeckeAlgebra.toTestFunction μ k
  change (∫ x, k' x * Hecke.TestFunction.convolution μ.inv
      (Hecke.TestFunction.inversion h') f x ∂μ) =
    ∫ x, (∫ y, h' y * k' (y⁻¹ * x) ∂μ) * f x ∂μ
  simp_rw [convolution_inv_apply]
  calc
    (∫ x, k' x * ∫ y, h' y * f (y * x) ∂μ ∂μ) =
        ∫ x, ∫ y, k' x * (h' y * f (y * x)) ∂μ ∂μ := by
      congr 1
      funext x
      exact (integral_const_mul _ _).symm
    _ = ∫ y, ∫ x, k' x * (h' y * f (y * x)) ∂μ ∂μ := by
      apply integral_integral_swap_of_hasCompactSupport
      · exact (k'.continuous.comp continuous_fst).mul ((h'.continuous.comp continuous_snd).mul
          (f.continuous.comp (continuous_snd.mul continuous_fst)))
      · apply HasCompactSupport.of_support_subset_isCompact
          ((Hecke.TestFunction.isCompact_support k').prod (Hecke.TestFunction.isCompact_support h'))
        rintro ⟨x, y⟩ hp
        change k' x * (h' y * f (y * x)) ≠ 0 at hp
        exact ⟨left_ne_zero_of_mul hp, left_ne_zero_of_mul (right_ne_zero_of_mul hp)⟩
    _ = ∫ y, ∫ x, h' y * k' (y⁻¹ * x) * f x ∂μ ∂μ := by
      congr 1
      funext y
      rw [← integral_mul_left_eq_self (fun x => h' y * k' (y⁻¹ * x) * f x) y]
      congr 1
      funext x
      simp only [inv_mul_cancel_left]
      ring
    _ = ∫ x, ∫ y, h' y * k' (y⁻¹ * x) * f x ∂μ ∂μ := by
      apply integral_integral_swap_of_hasCompactSupport
      · exact ((h'.continuous.comp continuous_fst).mul
          (k'.continuous.comp (continuous_fst.inv.mul continuous_snd))).mul
          (f.continuous.comp continuous_snd)
      · apply HasCompactSupport.of_support_subset_isCompact
          ((Hecke.TestFunction.isCompact_support h').prod (Hecke.TestFunction.isCompact_support f))
        rintro ⟨y, x⟩ hp
        change h' y * k' (y⁻¹ * x) * f x ≠ 0 at hp
        exact ⟨left_ne_zero_of_mul (left_ne_zero_of_mul hp), right_ne_zero_of_mul hp⟩
    _ = ∫ x, (∫ y, h' y * k' (y⁻¹ * x) ∂μ) * f x ∂μ := by
      congr 1
      funext x
      exact integral_mul_const _ _

/-- The two test operators defining the full left and right actions commute. -/
theorem leftTest_rightTest_comm (h e f : SchwartzBruhat G) :
    Hecke.TestFunction.convolution μ
        (Hecke.TestFunction.convolution μ.inv (Hecke.TestFunction.inversion h) f)
        (Hecke.TestFunction.inversion e) =
      Hecke.TestFunction.convolution μ.inv (Hecke.TestFunction.inversion h)
        (Hecke.TestFunction.convolution μ f (Hecke.TestFunction.inversion e)) := by
  ext x
  rw [convolution_inversion_apply, convolution_inv_apply]
  simp_rw [convolution_inv_apply, convolution_inversion_apply]
  calc
    (∫ z, (∫ y, h y * f (y * (x * z)) ∂μ) * e z ∂μ) =
        ∫ z, ∫ y, h y * f (y * (x * z)) * e z ∂μ ∂μ := by
      congr 1
      funext z
      exact (integral_mul_const _ _).symm
    _ = ∫ y, ∫ z, h y * f (y * (x * z)) * e z ∂μ ∂μ := by
      apply integral_integral_swap_of_hasCompactSupport
      · exact ((h.continuous.comp continuous_snd).mul (f.continuous.comp
          (continuous_snd.mul (continuous_const.mul continuous_fst)))).mul
          (e.continuous.comp continuous_fst)
      · apply HasCompactSupport.of_support_subset_isCompact
          ((Hecke.TestFunction.isCompact_support e).prod (Hecke.TestFunction.isCompact_support h))
        rintro ⟨z, y⟩ hp
        change h y * f (y * (x * z)) * e z ≠ 0 at hp
        exact ⟨right_ne_zero_of_mul hp, left_ne_zero_of_mul (left_ne_zero_of_mul hp)⟩
    _ = ∫ y, h y * ∫ z, f (y * x * z) * e z ∂μ ∂μ := by
      congr 1
      funext y
      rw [← integral_const_mul]
      congr 1
      funext z
      rw [mul_assoc y x z]
      ring

/-- Mixed associativity of the full actions: `h*(T*e) = (h*T)*e`. -/
theorem leftHecke_rightHecke_comm (T : Distribution G) (h e : Hecke.HeckeAlgebra μ) :
    leftHeckeConvolution μ h (rightHeckeConvolution μ T e) =
      rightHeckeConvolution μ (leftHeckeConvolution μ h T) e := by
  ext f
  exact congrArg T (leftTest_rightTest_comm μ (Hecke.HeckeAlgebra.toTestFunction μ h)
    (Hecke.HeckeAlgebra.toTestFunction μ e) f)

/-- The Dirac distribution at the identity acts as the Hecke density itself. -/
theorem rightHeckeConvolution_dirac_one (h : Hecke.HeckeAlgebra μ) :
    rightHeckeConvolution μ (dirac 1) h = heckeDistribution μ h := by
  ext f
  rw [rightHeckeConvolution_apply, dirac_apply, convolution_inversion_apply,
    heckeDistribution_apply]
  congr 1
  funext y
  rw [one_mul, mul_comm]
  rfl

variable [T2Space G]

/-- The full right action has the kernel `x ↦ T(y ↦ h(y⁻¹x))` against left Haar measure,
for every algebraic distribution. -/
theorem rightHeckeConvolution_apply_eq_integral (D : Distribution G)
    (h : Hecke.HeckeAlgebra μ) (f : SchwartzBruhat G) :
    rightHeckeConvolution μ D h f =
      ∫ x, leftConvolveTest D (Hecke.HeckeAlgebra.toTestFunction μ h) x * f x ∂μ := by
  let h' : SchwartzBruhat G := Hecke.HeckeAlgebra.toTestFunction μ h
  rw [rightHeckeConvolution_apply]
  have hk : Hecke.TestFunction.convolution μ f (Hecke.TestFunction.inversion h') =
      SchwartzBruhat.partialIntegral (leftDensityChangedKernel h' f) μ := by
    ext y
    rw [Hecke.TestFunction.convolution_apply, SchwartzBruhat.partialIntegral_apply]
    congr 1
    funext x
    simp only [leftDensityChangedKernel, SchwartzBruhat.compLeftInverse_apply,
      SchwartzBruhat.tensor_apply, Hecke.TestFunction.inversion_apply, mul_inv_rev, inv_inv]
    exact mul_comm _ _
  change D (Hecke.TestFunction.convolution μ f (Hecke.TestFunction.inversion h')) = _
  rw [hk, distribution_partialIntegral]
  congr 1
  funext x
  have he : SchwartzBruhat.sliceFst (leftDensityChangedKernel h' f) x =
      f x • Hecke.TestFunction.leftTranslate x (Hecke.TestFunction.inversion h') := by
    ext y
    simp only [SchwartzBruhat.sliceFst_apply, leftDensityChangedKernel,
      SchwartzBruhat.compLeftInverse_apply, SchwartzBruhat.tensor_apply]
    change h' (y⁻¹ * x) * f x = f x * h' ((x⁻¹ * y)⁻¹)
    rw [mul_inv_rev, inv_inv, mul_comm]
  rw [he, map_smul, smul_eq_mul, mul_comm]
  rfl

variable [LocallyCompactSpace G] [TotallyDisconnectedSpace G]

omit [IsTopologicalGroup G] in
/-- Integration against Hecke densities is faithful. -/
theorem heckeDistribution_injective : Function.Injective (heckeDistribution μ) := by
  intro k k' hkk
  have hloc := RenardHaar.density_injective μ
    (a₁ := ⟨(Hecke.HeckeAlgebra.toTestFunction μ k : G → ℂ),
      (Hecke.HeckeAlgebra.toTestFunction μ k).locallyConstant⟩)
    (a₂ := ⟨(Hecke.HeckeAlgebra.toTestFunction μ k' : G → ℂ),
      (Hecke.HeckeAlgebra.toTestFunction μ k').locallyConstant⟩) hkk
  apply Hecke.HeckeAlgebra.ext
  intro x
  exact congrArg (fun g : LocallyConstant G ℂ => g x) hloc

/-- On compactly supported distributions, the full right action is the compact
convolution with the Hecke density. -/
theorem rightHeckeConvolution_compact (T : compactlySupported (X := G))
    (h : Hecke.HeckeAlgebra μ) :
    rightHeckeConvolution μ (T : Distribution G) h =
      (convolution T (compactTestDensity μ (Hecke.HeckeAlgebra.toTestFunction μ h)) :
        Distribution G) := by
  rw [convolution_testDensity_left]
  ext f
  rw [rightHeckeConvolution_apply_eq_integral, testDensity_apply]
  rfl

/-- Right-essentially-compact distributions send Hecke densities to Hecke densities. -/
theorem exists_heckeDistribution_eq {T : Distribution G}
    (hT : T ∈ rightEssentiallyCompact μ) (h : Hecke.HeckeAlgebra μ) :
    ∃ k : Hecke.HeckeAlgebra μ, heckeDistribution μ k = rightHeckeConvolution μ T h := by
  let g : LocallyConstant G ℂ :=
    ⟨leftConvolveTest T (Hecke.HeckeAlgebra.toTestFunction μ h),
      leftConvolveTest_locallyConstant T _⟩
  have hdens : rightHeckeConvolution μ T h = density μ g := by
    ext f
    rw [rightHeckeConvolution_apply_eq_integral, density_apply]
    rfl
  have hsupp : IsCompact (Function.support g) := by
    rw [← RenardHaar.density_support μ g, ← hdens]
    exact hT h
  have hclosed : IsClosed (Function.support g) :=
    (g.isLocallyConstant.isClopen_fiber 0).compl.isClosed
  let k : SchwartzBruhat G := ⟨(g : G → ℂ), g.isLocallyConstant,
    HasCompactSupport.intro' hsupp hclosed (fun x hx => Function.notMem_support.mp hx)⟩
  refine ⟨(Hecke.HeckeAlgebra.toTestFunction μ).symm k, ?_⟩
  rw [hdens]
  ext f
  exact rfl

/-- Compactly supported distributions are right essentially compact. -/
theorem compact_mem_rightEssentiallyCompact (T : compactlySupported (X := G)) :
    (T : Distribution G) ∈ rightEssentiallyCompact μ := by
  intro h
  change rightHeckeConvolution μ (T : Distribution G) h ∈ compactlySupported
  rw [rightHeckeConvolution_compact]
  exact (convolution T _).property

/-- Hecke densities are right essentially compact. -/
theorem heckeDistribution_mem_rightEssentiallyCompact (k : Hecke.HeckeAlgebra μ) :
    heckeDistribution μ k ∈ rightEssentiallyCompact μ := by
  intro h
  change rightHeckeConvolution μ (heckeDistribution μ k) h ∈ compactlySupported
  rw [rightHeckeConvolution_heckeDistribution]
  exact RenardHaar.testDensity_compactlySupported μ _

/-- The Dirac distribution at the identity is right essentially compact. -/
theorem dirac_one_mem_rightEssentiallyCompact :
    (dirac (1 : G) : Distribution G) ∈ rightEssentiallyCompact μ := by
  intro h
  change rightHeckeConvolution μ (dirac 1) h ∈ compactlySupported
  rw [rightHeckeConvolution_dirac_one]
  exact RenardHaar.testDensity_compactlySupported μ _

end Laws

end Langlands.HarmonicAnalysis.Distribution.RenardCompletion

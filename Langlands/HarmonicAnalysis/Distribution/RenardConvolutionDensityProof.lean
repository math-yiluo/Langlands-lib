import Langlands.HarmonicAnalysis.Distribution.RenardConvolutionLawsProof

/-! # Haar densities and the actual Hecke convolution -/

noncomputable section

open MeasureTheory

namespace Langlands.HarmonicAnalysis.Distribution

universe uX uY uG

section Integration

variable {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]
  [T2Space X] [T2Space Y] [MeasurableSpace Y] [BorelSpace Y]
  (μ : Measure Y) [IsFiniteMeasureOnCompacts μ]

/-- Algebraic distribution evaluation commutes with the partial integral of a
product test, by the already proved finite-tensor Fubini theorem. -/
theorem distribution_partialIntegral (D : Distribution X) (k : SchwartzBruhat (X × Y)) :
    D (SchwartzBruhat.partialIntegral k μ) =
      ∫ y, D (SchwartzBruhat.sliceFst k y) ∂μ := by
  change tensor D (ofMeasure μ) k = (ofMeasure μ) (partialApplyFst D k)
  exact tensor_fubini D (ofMeasure μ) k

end Integration

section Density

variable {X : Type uX} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [TotallyDisconnectedSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ]

omit [LocallyCompactSpace X] [TotallyDisconnectedSpace X] in
theorem support_testDensity_subset (f : SchwartzBruhat X) :
    support (testDensity μ f) ⊆ Function.support (f : X → ℂ) := by
  apply support_subset_of_mem_supportedOn (Hecke.TestFunction.isCompact_support f).isClosed
  intro φ hφ
  change (∫ x, f x * φ x ∂μ) = 0
  apply integral_eq_zero_of_ae
  exact Filter.Eventually.of_forall fun x => by
    change f x * φ x = 0
    by_cases hx : f x = 0
    · simp [hx]
    · rw [hφ x hx, mul_zero]

/-- The original density distribution with its actual compact support witness. -/
def compactTestDensity (f : SchwartzBruhat X) : compactlySupported (X := X) :=
  ⟨testDensity μ f, (Hecke.TestFunction.isCompact_support f).of_isClosed_subset
    (isClosed_support _) (support_testDensity_subset μ f)⟩

theorem compactSupportPairing_testDensity (f : SchwartzBruhat X) (h : LocallyConstant X ℂ) :
    compactSupportPairing (compactTestDensity μ f) h = ∫ x, f x * h x ∂μ := by
  obtain ⟨φ, hφ⟩ := exists_testFunction_agrees_on_compact
    (Hecke.TestFunction.isCompact_support f) h
  rw [compactSupportPairing_eq_of_agrees (compactTestDensity μ f) h φ
    (fun x hx => hφ x (support_testDensity_subset μ f hx))]
  change (∫ x, f x * φ x ∂μ) = _
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change f x * φ x = f x * h x
    by_cases hx : f x = 0
    · simp [hx]
    · rw [hφ x hx]

end Density

section Kernels

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G]

/-- Compact product test `(x,y) ↦ f(y) φ(xy)`. -/
def leftDensityKernel (f φ : SchwartzBruhat G) : SchwartzBruhat (G × G) :=
  SchwartzBruhat.compLeftInverse (SchwartzBruhat.tensor f φ)
    (fun p : G × G => (p.2, p.1 * p.2))
    (fun p : G × G => (p.2 * p.1⁻¹, p.1))
    (continuous_snd.prodMk (continuous_fst.mul continuous_snd))
    ((continuous_snd.mul continuous_fst.inv).prodMk continuous_fst)
    (by intro p; ext <;> simp)

/-- Compact product test `(x,z) ↦ f(x⁻¹z) φ(z)`. -/
def leftDensityChangedKernel (f φ : SchwartzBruhat G) : SchwartzBruhat (G × G) :=
  SchwartzBruhat.compLeftInverse (SchwartzBruhat.tensor f φ)
    (fun p : G × G => (p.1⁻¹ * p.2, p.2))
    (fun p : G × G => (p.2 * p.1⁻¹, p.2))
    ((continuous_fst.inv.mul continuous_snd).prodMk continuous_snd)
    ((continuous_snd.mul continuous_fst.inv).prodMk continuous_snd)
    (by intro p; ext <;> simp)

/-- Compact product test `(y,x) ↦ f(x) φ(xy)`. -/
def rightDensityKernel (f φ : SchwartzBruhat G) : SchwartzBruhat (G × G) :=
  SchwartzBruhat.compLeftInverse (SchwartzBruhat.tensor f φ)
    (fun p : G × G => (p.2, p.2 * p.1))
    (fun p : G × G => (p.1⁻¹ * p.2, p.1))
    (continuous_snd.prodMk (continuous_snd.mul continuous_fst))
    ((continuous_fst.inv.mul continuous_snd).prodMk continuous_fst)
    (by intro p; ext <;> simp)

/-- Compact product test `(y,z) ↦ f(zy⁻¹) φ(z)`. -/
def rightDensityChangedKernel (f φ : SchwartzBruhat G) : SchwartzBruhat (G × G) :=
  SchwartzBruhat.compLeftInverse (SchwartzBruhat.tensor f φ)
    (fun p : G × G => (p.2 * p.1⁻¹, p.2))
    (fun p : G × G => (p.1⁻¹ * p.2, p.2))
    ((continuous_snd.mul continuous_fst.inv).prodMk continuous_snd)
    ((continuous_fst.inv.mul continuous_snd).prodMk continuous_snd)
    (by intro p; ext <;> simp [mul_assoc])

end Kernels

section Group

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G]

/-- The compact scalar test supplied by the proved regularity theorem. -/
def leftTestFunction (T : compactlySupported (X := G)) (f : SchwartzBruhat G) :
    SchwartzBruhat G :=
  ⟨leftConvolveTest (T : Distribution G) f, leftConvolveTest_locallyConstant _ _,
    leftConvolveTest_hasCompactSupport T f⟩

def rightTestFunction (f : SchwartzBruhat G) (T : compactlySupported (X := G)) :
    SchwartzBruhat G :=
  ⟨rightConvolveTest f (T : Distribution G), rightConvolveTest_locallyConstant _ _,
    rightConvolveTest_hasCompactSupport T f⟩

theorem convolution_testDensity_left (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    [μ.IsMulLeftInvariant] (T : compactlySupported (X := G)) (f : SchwartzBruhat G) :
    (convolution T (compactTestDensity μ f) : Distribution G) =
      testDensity μ (leftTestFunction T f) := by
  ext φ
  rw [convolution_eq_pairing]
  calc
    _ = (T : Distribution G) (SchwartzBruhat.partialIntegral (leftDensityKernel f φ) μ) := by
      apply compactSupportPairing_eq_of_agrees
      intro x _
      let h : LocallyConstant G ℂ := ⟨fun y => φ (x * y),
        φ.locallyConstant.comp_continuous (continuous_const.mul continuous_id)⟩
      change (∫ y, f y * h y ∂μ) = compactSupportPairing (compactTestDensity μ f) h
      exact (compactSupportPairing_testDensity μ f h).symm
    _ = (T : Distribution G)
        (SchwartzBruhat.partialIntegral (leftDensityChangedKernel f φ) μ) := by
      congr 1
      ext x
      change (∫ y, f y * φ (x * y) ∂μ) = ∫ z, f (x⁻¹ * z) * φ z ∂μ
      rw [← integral_mul_left_eq_self (fun z => f (x⁻¹ * z) * φ z) x]
      simp only [inv_mul_cancel_left]
    _ = ∫ z, (T : Distribution G)
        (SchwartzBruhat.sliceFst (leftDensityChangedKernel f φ) z) ∂μ :=
      distribution_partialIntegral μ _ _
    _ = _ := by
      change _ = ∫ z, leftConvolveTest (T : Distribution G) f z * φ z ∂μ
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        change (T : Distribution G) (SchwartzBruhat.sliceFst (leftDensityChangedKernel f φ) z) =
          leftConvolveTest (T : Distribution G) f z * φ z
        have he : SchwartzBruhat.sliceFst (leftDensityChangedKernel f φ) z =
            φ z • Hecke.TestFunction.leftTranslate z (Hecke.TestFunction.inversion f) := by
          ext x
          simp [leftDensityChangedKernel, mul_comm]
        rw [he, map_smul]
        exact mul_comm _ _

theorem convolution_testDensity_right (ν : Measure G) [IsFiniteMeasureOnCompacts ν]
    [ν.IsMulRightInvariant] (T : compactlySupported (X := G)) (f : SchwartzBruhat G) :
    (convolution (compactTestDensity ν f) T : Distribution G) =
      testDensity ν (rightTestFunction f T) := by
  ext φ
  rw [convolution_eq_pairing, compactPairing_swap]
  calc
    _ = (T : Distribution G) (SchwartzBruhat.partialIntegral (rightDensityKernel f φ) ν) := by
      apply compactSupportPairing_eq_of_agrees
      intro y _
      let h : LocallyConstant G ℂ := ⟨fun x => φ (x * y),
        φ.locallyConstant.comp_continuous (continuous_id.mul continuous_const)⟩
      change (∫ x, f x * h x ∂ν) = compactSupportPairing (compactTestDensity ν f) h
      exact (compactSupportPairing_testDensity ν f h).symm
    _ = (T : Distribution G)
        (SchwartzBruhat.partialIntegral (rightDensityChangedKernel f φ) ν) := by
      congr 1
      ext y
      change (∫ x, f x * φ (x * y) ∂ν) = ∫ z, f (z * y⁻¹) * φ z ∂ν
      rw [← integral_mul_right_eq_self (fun z => f (z * y⁻¹) * φ z) y]
      simp only [mul_inv_cancel_right]
    _ = ∫ z, (T : Distribution G)
        (SchwartzBruhat.sliceFst (rightDensityChangedKernel f φ) z) ∂ν :=
      distribution_partialIntegral ν _ _
    _ = _ := by
      change _ = ∫ z, rightConvolveTest f (T : Distribution G) z * φ z ∂ν
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        change (T : Distribution G) (SchwartzBruhat.sliceFst (rightDensityChangedKernel f φ) z) =
          rightConvolveTest f (T : Distribution G) z * φ z
        have he : SchwartzBruhat.sliceFst (rightDensityChangedKernel f φ) z =
            φ z • Hecke.TestFunction.rightTranslate z⁻¹ (Hecke.TestFunction.inversion f) := by
          ext y
          simp [rightDensityChangedKernel, mul_comm]
        rw [he, map_smul]
        exact mul_comm _ _

end Group

namespace RenardConvolution

theorem haarDensity : HaarDensityStatement.{uG} := by
  intro G _ _ _ _ _ _ _ _ μ ν _ _ _ T f
  exact ⟨compactTestDensity μ f, compactTestDensity ν f, rfl, rfl,
    leftTestFunction T f, rightTestFunction f T, rfl, rfl,
    convolution_testDensity_left μ T f, convolution_testDensity_right ν T f⟩

theorem heckeCompatibility : HeckeCompatibilityStatement.{uG} := by
  intro G _ _ _ _ _ _ _ _ μ _ f g
  refine ⟨compactTestDensity μ f, compactTestDensity μ g, rfl, rfl, ?_⟩
  rw [convolution_testDensity_left]
  congr 1
  ext x
  change (∫ y, f y *
    (Hecke.TestFunction.leftTranslate x (Hecke.TestFunction.inversion g)) y ∂μ) = _
  simp only [Hecke.TestFunction.leftTranslate_apply, Hecke.TestFunction.inversion_apply,
    mul_inv_rev, inv_inv, Hecke.TestFunction.convolution_apply]

end RenardConvolution
end Langlands.HarmonicAnalysis.Distribution

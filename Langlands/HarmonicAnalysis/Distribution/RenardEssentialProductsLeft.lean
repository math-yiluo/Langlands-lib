import Langlands.HarmonicAnalysis.Distribution.RenardEssentialProductsKernels

/-! # Renard II.3.13: the product on left-essentially-compact distributions -/

set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory

namespace Langlands.HarmonicAnalysis.Distribution.RenardEssentialProducts

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]

/-- A left Hecke product of a left-essentially-compact distribution is a Hecke density. -/
theorem exists_hecke_eq_left {T : Distribution G} (hT : T ∈ leftEssentiallyCompact μ)
    (h : Hecke.HeckeAlgebra μ) :
    ∃ k : Hecke.HeckeAlgebra μ, heckeDistribution μ k = leftHeckeConvolution μ h T := by
  obtain ⟨g, hg⟩ := exists_testDensity_eq_left μ hT h
  exact ⟨(Hecke.HeckeAlgebra.toTestFunction μ).symm g, hg⟩

/-- For left `K`-invariant `f`, the left kernel of `T` is a left Hecke convolution of `f`
with a density of `e_K * T`. -/
theorem leftKernel_eq_convolution (T : Distribution G) (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (f : SchwartzBruhat G) (hf : ∀ k ∈ K, ∀ x, f (k * x) = f x)
    (k : SchwartzBruhat G)
    (hk : testDensity μ k =
      leftHeckeConvolution μ (Hecke.HeckeAlgebra.normalizedIndicator μ K hK) T) :
    leftKernel T f =
      ⇑(Hecke.TestFunction.convolution μ.inv (Hecke.TestFunction.inversion k) f) := by
  rw [← leftKernel_leftHecke_normalizedIndicator μ T K hK f hf, ← hk,
    leftKernel_testDensity]

theorem leftKernel_hasCompactSupport {T : Distribution G}
    (hT : T ∈ leftEssentiallyCompact μ) (f : SchwartzBruhat G) :
    HasCompactSupport (leftKernel T f) := by
  obtain ⟨K, hK, hl, -⟩ := exists_biInvariant f
  obtain ⟨k, hk⟩ := exists_testDensity_eq_left μ hT
    (Hecke.HeckeAlgebra.normalizedIndicator μ K hK)
  rw [leftKernel_eq_convolution μ T K hK f hl k hk]
  exact (Hecke.TestFunction.convolution μ.inv (Hecke.TestFunction.inversion k) f).hasCompactSupport

/-- The test `y ↦ T(x ↦ f(xy))` for left-essentially-compact `T`. -/
def lconv (T : leftEssentiallyCompact μ) (f : SchwartzBruhat G) : SchwartzBruhat G :=
  ⟨leftKernel (T : Distribution G) f, leftKernel_locallyConstant _ _,
    leftKernel_hasCompactSupport μ T.property f⟩

@[simp] theorem lconv_apply (T : leftEssentiallyCompact μ) (f : SchwartzBruhat G) (y : G) :
    lconv μ T f y = leftKernel (T : Distribution G) f y := rfl

theorem lconv_add_test (T : leftEssentiallyCompact μ) (f g : SchwartzBruhat G) :
    lconv μ T (f + g) = lconv μ T f + lconv μ T g := by
  ext y
  simp [leftKernel_apply, map_add]

theorem lconv_smul_test (T : leftEssentiallyCompact μ) (c : ℂ) (f : SchwartzBruhat G) :
    lconv μ T (c • f) = c • lconv μ T f := by
  ext y
  simp [leftKernel_apply, map_smul]

theorem lconv_add (T S : leftEssentiallyCompact μ) (f : SchwartzBruhat G) :
    lconv μ (T + S) f = lconv μ T f + lconv μ S f := by
  ext y
  rfl

theorem lconv_smul (c : ℂ) (T : leftEssentiallyCompact μ) (f : SchwartzBruhat G) :
    lconv μ (c • T) f = c • lconv μ T f := by
  ext y
  rfl

/-- `lconv T` as a linear endomorphism of the test space. -/
def lconvLinear (T : leftEssentiallyCompact μ) : SchwartzBruhat G →ₗ[ℂ] SchwartzBruhat G where
  toFun := lconv μ T
  map_add' := lconv_add_test μ T
  map_smul' c f := lconv_smul_test μ T c f

/-- The source formula `(T*U)(f) = U_y T_x f(xy)` as a full distribution. -/
def pLDist (T U : leftEssentiallyCompact μ) : Distribution G :=
  (U : Distribution G).comp (lconvLinear μ T)

theorem pLDist_apply (T U : leftEssentiallyCompact μ) (f : SchwartzBruhat G) :
    pLDist μ T U f = (U : Distribution G) (lconv μ T f) := rfl

/-- Left convolution by Hecke densities passes through `lconv`. -/
theorem lconv_convolution (T : leftEssentiallyCompact μ) (h k : Hecke.HeckeAlgebra μ)
    (hk : heckeDistribution μ k = leftHeckeConvolution μ h (T : Distribution G))
    (f : SchwartzBruhat G) :
    lconv μ T (Hecke.TestFunction.convolution μ.inv
        (Hecke.TestFunction.inversion (Hecke.HeckeAlgebra.toTestFunction μ h)) f) =
      Hecke.TestFunction.convolution μ.inv
        (Hecke.TestFunction.inversion (Hecke.HeckeAlgebra.toTestFunction μ k)) f := by
  ext y
  have he : leftKernel (leftHeckeConvolution μ h (T : Distribution G)) f y =
      Hecke.TestFunction.convolution μ.inv
        (Hecke.TestFunction.inversion (Hecke.HeckeAlgebra.toTestFunction μ k)) f y := by
    rw [← hk]
    change leftKernel (testDensity μ (Hecke.HeckeAlgebra.toTestFunction μ k)) f y = _
    rw [leftKernel_testDensity]
  rw [← he, lconv_apply, leftKernel_apply, rightTranslate_convolution_inv_inversion]
  rfl

theorem leftHecke_pLDist (T U : leftEssentiallyCompact μ) (h k : Hecke.HeckeAlgebra μ)
    (hk : heckeDistribution μ k = leftHeckeConvolution μ h (T : Distribution G)) :
    leftHeckeConvolution μ h (pLDist μ T U) =
      leftHeckeConvolution μ k (U : Distribution G) := by
  ext f
  rw [leftHeckeConvolution_apply, leftHeckeConvolution_apply, pLDist_apply,
    lconv_convolution μ T h k hk f]

theorem pLDist_mem (T U : leftEssentiallyCompact μ) :
    pLDist μ T U ∈ leftEssentiallyCompact μ := by
  intro h
  obtain ⟨k, hk⟩ := exists_hecke_eq_left μ T.property h
  change leftHeckeConvolution μ h (pLDist μ T U) ∈ compactlySupported
  rw [leftHecke_pLDist μ T U h k hk]
  exact U.property k

/-- The left product on left-essentially-compact distributions. -/
def pL : leftEssentiallyCompact μ →ₗ[ℂ]
    leftEssentiallyCompact μ →ₗ[ℂ] leftEssentiallyCompact μ :=
  LinearMap.mk₂ ℂ (fun T U => ⟨pLDist μ T U, pLDist_mem μ T U⟩)
    (fun T₁ T₂ U => Subtype.ext (LinearMap.ext fun f => by
      change (U : Distribution G) (lconv μ (T₁ + T₂) f) =
        (U : Distribution G) (lconv μ T₁ f) + (U : Distribution G) (lconv μ T₂ f)
      rw [lconv_add, map_add]))
    (fun c T U => Subtype.ext (LinearMap.ext fun f => by
      change (U : Distribution G) (lconv μ (c • T) f) = c • (U : Distribution G) (lconv μ T f)
      rw [lconv_smul, map_smul]))
    (fun T U₁ U₂ => Subtype.ext (LinearMap.ext fun f => rfl))
    (fun c T U => Subtype.ext (LinearMap.ext fun f => rfl))

theorem pL_apply (T U : leftEssentiallyCompact μ) (f : SchwartzBruhat G) :
    (pL μ T U : Distribution G) f = (U : Distribution G) (lconv μ T f) := rfl

theorem lconv_lconv (T U : leftEssentiallyCompact μ) (f : SchwartzBruhat G) :
    lconv μ U (lconv μ T f) = lconv μ (pL μ T U) f := by
  ext y
  rw [lconv_apply, lconv_apply, leftKernel_apply, leftKernel_apply, pL_apply]
  congr 1
  ext z
  rw [Hecke.TestFunction.rightTranslate_apply, lconv_apply, lconv_apply, leftKernel_apply,
    leftKernel_apply]
  congr 1
  ext w
  simp [mul_assoc]

theorem pL_assoc (T U V : leftEssentiallyCompact μ) :
    pL μ (pL μ T U) V = pL μ T (pL μ U V) := by
  apply Subtype.ext
  ext f
  rw [pL_apply, pL_apply, pL_apply, lconv_lconv]

theorem dirac_mem_left : dirac (1 : G) ∈ leftEssentiallyCompact μ :=
  compactlySupported_le_left μ (compactDirac (1 : G)).property

theorem heckeDistribution_mem_left (h : Hecke.HeckeAlgebra μ) :
    heckeDistribution μ h ∈ leftEssentiallyCompact μ :=
  compactlySupported_le_left μ
    (RenardHaar.testDensity_compactlySupported μ (Hecke.HeckeAlgebra.toTestFunction μ h))

theorem lconv_heckeDistribution (h : Hecke.HeckeAlgebra μ) (f : SchwartzBruhat G) :
    lconv μ ⟨heckeDistribution μ h, heckeDistribution_mem_left μ h⟩ f =
      Hecke.TestFunction.convolution μ.inv
        (Hecke.TestFunction.inversion (Hecke.HeckeAlgebra.toTestFunction μ h)) f := by
  ext y
  rw [lconv_apply]
  change leftKernel (testDensity μ (Hecke.HeckeAlgebra.toTestFunction μ h)) f y = _
  rw [leftKernel_testDensity]

/-- Renard's left product satisfies the complete published left specification. -/
theorem pL_spec : LeftProductSpecification μ (pL μ) := by
  refine ⟨⟨pL_assoc μ, ?_, ?_, ?_⟩, ?_, ?_⟩
  · refine ⟨⟨dirac 1, dirac_mem_left μ⟩, rfl, fun T => ⟨?_, ?_⟩⟩
    · apply Subtype.ext
      ext f
      rw [pL_apply]
      congr 1
      ext y
      rw [lconv_apply, leftKernel_apply]
      simp
    · apply Subtype.ext
      ext f
      rw [pL_apply]
      change leftKernel (T : Distribution G) f 1 = _
      rw [leftKernel_apply, Hecke.TestFunction.rightTranslate_one]
  · intro T U
    refine ⟨⟨T, compactlySupported_le_left μ T.property⟩,
      ⟨U, compactlySupported_le_left μ U.property⟩, rfl, rfl, ?_⟩
    ext f
    rw [pL_apply]
    exact (convolution_apply_leftKernel T U f _ (fun y => rfl)).symm
  · intro T h
    refine ⟨⟨heckeDistribution μ h, heckeDistribution_mem_left μ h⟩, rfl, ?_, ?_⟩
    · ext f
      rw [pL_apply, rightHeckeConvolution_apply, rightHecke_eval]
      rfl
    · ext f
      rw [pL_apply, lconv_heckeDistribution, leftHeckeConvolution_apply]
  · intro T U f K hK hf
    have hl := (leftConvolveTest_eq_iff K hK f).mp hf
    obtain ⟨k, hk⟩ := exists_hecke_eq_left μ T.property
      (Hecke.HeckeAlgebra.normalizedIndicator μ K hK)
    refine ⟨k, hk, ?_⟩
    rw [pL_apply, leftHeckeConvolution_apply]
    congr 1
    ext y
    rw [lconv_apply, leftKernel_eq_convolution μ (T : Distribution G) K hK f hl
      (Hecke.HeckeAlgebra.toTestFunction μ k) hk]
  · intro T U h
    obtain ⟨k, hk⟩ := exists_hecke_eq_left μ T.property h
    exact ⟨k, hk, leftHecke_pLDist μ T U h k hk⟩

/-- Every product with the published left specification is Renard's left product. -/
theorem eq_pL (p : leftEssentiallyCompact μ →ₗ[ℂ]
      leftEssentiallyCompact μ →ₗ[ℂ] leftEssentiallyCompact μ)
    (hp : LeftProductSpecification μ p) : p = pL μ := by
  apply LinearMap.ext
  intro T
  apply LinearMap.ext
  intro U
  apply Subtype.ext
  ext f
  obtain ⟨K, hK, hl, -⟩ := exists_biInvariant f
  obtain ⟨h, hh, hpf⟩ := hp.2.1 T U f K hK ((leftConvolveTest_eq_iff K hK f).mpr hl)
  rw [hpf, leftHeckeConvolution_apply, pL_apply]
  congr 1
  ext y
  rw [lconv_apply, leftKernel_eq_convolution μ (T : Distribution G) K hK f hl
    (Hecke.HeckeAlgebra.toTestFunction μ h) hh]

theorem left_existsUnique :
    ∃! p : leftEssentiallyCompact μ →ₗ[ℂ]
        leftEssentiallyCompact μ →ₗ[ℂ] leftEssentiallyCompact μ,
      LeftProductSpecification μ p :=
  ⟨pL μ, pL_spec μ, fun p hp => eq_pL μ p hp⟩

end Langlands.HarmonicAnalysis.Distribution.RenardEssentialProducts

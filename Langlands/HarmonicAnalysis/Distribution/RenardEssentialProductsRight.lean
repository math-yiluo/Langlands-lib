import Langlands.HarmonicAnalysis.Distribution.RenardEssentialProductsKernels

/-! # Renard II.3.13: the product on right-essentially-compact distributions -/

set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory

namespace Langlands.HarmonicAnalysis.Distribution.RenardEssentialProducts

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]

/-- A right Hecke product of a right-essentially-compact distribution is a Hecke density. -/
theorem exists_hecke_eq_right {U : Distribution G} (hU : U ∈ rightEssentiallyCompact μ)
    (h : Hecke.HeckeAlgebra μ) :
    ∃ k : Hecke.HeckeAlgebra μ, heckeDistribution μ k = rightHeckeConvolution μ U h := by
  obtain ⟨g, hg⟩ := exists_testDensity_eq_right μ hU h
  exact ⟨(Hecke.HeckeAlgebra.toTestFunction μ).symm g, hg⟩

/-- For right `K`-invariant `f`, the right kernel of `U` is a right Hecke convolution of `f`
with a density of `U * e_K`. -/
theorem rightKernel_eq_convolution (U : Distribution G) (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (f : SchwartzBruhat G) (hf : ∀ k ∈ K, ∀ x, f (x * k) = f x)
    (k : SchwartzBruhat G)
    (hk : testDensity μ k =
      rightHeckeConvolution μ U (Hecke.HeckeAlgebra.normalizedIndicator μ K hK)) :
    rightKernel U f =
      ⇑(Hecke.TestFunction.convolution μ f (Hecke.TestFunction.inversion k)) := by
  rw [← rightKernel_rightHecke_normalizedIndicator μ U K hK f hf, ← hk,
    rightKernel_testDensity]

theorem rightKernel_hasCompactSupport {U : Distribution G}
    (hU : U ∈ rightEssentiallyCompact μ) (f : SchwartzBruhat G) :
    HasCompactSupport (rightKernel U f) := by
  obtain ⟨K, hK, -, hr⟩ := exists_biInvariant f
  obtain ⟨k, hk⟩ := exists_testDensity_eq_right μ hU
    (Hecke.HeckeAlgebra.normalizedIndicator μ K hK)
  rw [rightKernel_eq_convolution μ U K hK f hr k hk]
  exact (Hecke.TestFunction.convolution μ f (Hecke.TestFunction.inversion k)).hasCompactSupport

/-- The test `x ↦ U(y ↦ f(xy))` for right-essentially-compact `U`. -/
def rconv (U : rightEssentiallyCompact μ) (f : SchwartzBruhat G) : SchwartzBruhat G :=
  ⟨rightKernel (U : Distribution G) f, rightKernel_locallyConstant _ _,
    rightKernel_hasCompactSupport μ U.property f⟩

@[simp] theorem rconv_apply (U : rightEssentiallyCompact μ) (f : SchwartzBruhat G) (x : G) :
    rconv μ U f x = rightKernel (U : Distribution G) f x := rfl

theorem rconv_add_test (U : rightEssentiallyCompact μ) (f g : SchwartzBruhat G) :
    rconv μ U (f + g) = rconv μ U f + rconv μ U g := by
  ext x
  simp [rightKernel_apply, map_add]

theorem rconv_smul_test (U : rightEssentiallyCompact μ) (c : ℂ) (f : SchwartzBruhat G) :
    rconv μ U (c • f) = c • rconv μ U f := by
  ext x
  simp [rightKernel_apply, map_smul]

theorem rconv_add (U V : rightEssentiallyCompact μ) (f : SchwartzBruhat G) :
    rconv μ (U + V) f = rconv μ U f + rconv μ V f := by
  ext x
  rfl

theorem rconv_smul (c : ℂ) (U : rightEssentiallyCompact μ) (f : SchwartzBruhat G) :
    rconv μ (c • U) f = c • rconv μ U f := by
  ext x
  rfl

/-- `rconv U` as a linear endomorphism of the test space. -/
def rconvLinear (U : rightEssentiallyCompact μ) : SchwartzBruhat G →ₗ[ℂ] SchwartzBruhat G where
  toFun := rconv μ U
  map_add' := rconv_add_test μ U
  map_smul' c f := rconv_smul_test μ U c f

/-- The source formula `(T*U)(f) = T_x U_y f(xy)` as a full distribution. -/
def pRDist (T U : rightEssentiallyCompact μ) : Distribution G :=
  (T : Distribution G).comp (rconvLinear μ U)

theorem pRDist_apply (T U : rightEssentiallyCompact μ) (f : SchwartzBruhat G) :
    pRDist μ T U f = (T : Distribution G) (rconv μ U f) := rfl

/-- Right translation by Hecke densities passes through `rconv`. -/
theorem rconv_convolution (U : rightEssentiallyCompact μ) (h k : Hecke.HeckeAlgebra μ)
    (hk : heckeDistribution μ k = rightHeckeConvolution μ (U : Distribution G) h)
    (f : SchwartzBruhat G) :
    rconv μ U (Hecke.TestFunction.convolution μ f
        (Hecke.TestFunction.inversion (Hecke.HeckeAlgebra.toTestFunction μ h))) =
      Hecke.TestFunction.convolution μ f
        (Hecke.TestFunction.inversion (Hecke.HeckeAlgebra.toTestFunction μ k)) := by
  ext x
  have he : rightKernel (rightHeckeConvolution μ (U : Distribution G) h) f x =
      Hecke.TestFunction.convolution μ f
        (Hecke.TestFunction.inversion (Hecke.HeckeAlgebra.toTestFunction μ k)) x := by
    rw [← hk]
    change rightKernel (testDensity μ (Hecke.HeckeAlgebra.toTestFunction μ k)) f x = _
    rw [rightKernel_testDensity]
  rw [← he, rconv_apply, rightKernel_apply, leftTranslate_convolution_inversion]
  rfl

theorem rightHecke_pRDist (T U : rightEssentiallyCompact μ) (h k : Hecke.HeckeAlgebra μ)
    (hk : heckeDistribution μ k = rightHeckeConvolution μ (U : Distribution G) h) :
    rightHeckeConvolution μ (pRDist μ T U) h =
      rightHeckeConvolution μ (T : Distribution G) k := by
  ext f
  rw [rightHeckeConvolution_apply, rightHeckeConvolution_apply, pRDist_apply,
    rconv_convolution μ U h k hk f]

theorem pRDist_mem (T U : rightEssentiallyCompact μ) :
    pRDist μ T U ∈ rightEssentiallyCompact μ := by
  intro h
  obtain ⟨k, hk⟩ := exists_hecke_eq_right μ U.property h
  change rightHeckeConvolution μ (pRDist μ T U) h ∈ compactlySupported
  rw [rightHecke_pRDist μ T U h k hk]
  exact T.property k

/-- The right product on right-essentially-compact distributions. -/
def pR : rightEssentiallyCompact μ →ₗ[ℂ]
    rightEssentiallyCompact μ →ₗ[ℂ] rightEssentiallyCompact μ :=
  LinearMap.mk₂ ℂ (fun T U => ⟨pRDist μ T U, pRDist_mem μ T U⟩)
    (fun T₁ T₂ U => Subtype.ext (LinearMap.ext fun f => rfl))
    (fun c T U => Subtype.ext (LinearMap.ext fun f => rfl))
    (fun T U₁ U₂ => Subtype.ext (LinearMap.ext fun f => by
      change (T : Distribution G) (rconv μ (U₁ + U₂) f) =
        (T : Distribution G) (rconv μ U₁ f) + (T : Distribution G) (rconv μ U₂ f)
      rw [rconv_add, map_add]))
    (fun c T U => Subtype.ext (LinearMap.ext fun f => by
      change (T : Distribution G) (rconv μ (c • U) f) = c • (T : Distribution G) (rconv μ U f)
      rw [rconv_smul, map_smul]))

theorem pR_apply (T U : rightEssentiallyCompact μ) (f : SchwartzBruhat G) :
    (pR μ T U : Distribution G) f = (T : Distribution G) (rconv μ U f) := rfl

theorem rconv_rconv (U V : rightEssentiallyCompact μ) (f : SchwartzBruhat G) :
    rconv μ U (rconv μ V f) = rconv μ (pR μ U V) f := by
  ext x
  rw [rconv_apply, rconv_apply, rightKernel_apply, rightKernel_apply, pR_apply]
  congr 1
  ext y
  rw [leftTranslate_inv_apply, rconv_apply, rconv_apply, rightKernel_apply, rightKernel_apply]
  congr 1
  ext z
  simp [mul_assoc]

theorem pR_assoc (T U V : rightEssentiallyCompact μ) :
    pR μ (pR μ T U) V = pR μ T (pR μ U V) := by
  apply Subtype.ext
  ext f
  rw [pR_apply, pR_apply, pR_apply, rconv_rconv]

theorem dirac_mem_right : dirac (1 : G) ∈ rightEssentiallyCompact μ :=
  compactlySupported_le_right μ (compactDirac (1 : G)).property

theorem heckeDistribution_mem_right (h : Hecke.HeckeAlgebra μ) :
    heckeDistribution μ h ∈ rightEssentiallyCompact μ :=
  compactlySupported_le_right μ
    (RenardHaar.testDensity_compactlySupported μ (Hecke.HeckeAlgebra.toTestFunction μ h))

theorem rconv_heckeDistribution (h : Hecke.HeckeAlgebra μ) (f : SchwartzBruhat G) :
    rconv μ ⟨heckeDistribution μ h, heckeDistribution_mem_right μ h⟩ f =
      Hecke.TestFunction.convolution μ f
        (Hecke.TestFunction.inversion (Hecke.HeckeAlgebra.toTestFunction μ h)) := by
  ext x
  rw [rconv_apply]
  change rightKernel (testDensity μ (Hecke.HeckeAlgebra.toTestFunction μ h)) f x = _
  rw [rightKernel_testDensity]

theorem pR_dirac_left (T : rightEssentiallyCompact μ) :
    pR μ ⟨dirac 1, dirac_mem_right μ⟩ T = T := by
  apply Subtype.ext
  ext f
  rw [pR_apply]
  change rightKernel (T : Distribution G) f 1 = _
  rw [rightKernel_apply, inv_one, Hecke.TestFunction.leftTranslate_one]

theorem pR_dirac_right (T : rightEssentiallyCompact μ) :
    pR μ T ⟨dirac 1, dirac_mem_right μ⟩ = T := by
  apply Subtype.ext
  ext f
  rw [pR_apply]
  congr 1
  ext x
  rw [rconv_apply, rightKernel_apply]
  simp

/-- On compact distributions the right product is the compact convolution. -/
theorem pR_compact (T U : compactlySupported (X := G)) :
    (pR μ ⟨T, compactlySupported_le_right μ T.property⟩
        ⟨U, compactlySupported_le_right μ U.property⟩ : Distribution G) =
      (convolution T U : Distribution G) := by
  ext f
  rw [pR_apply]
  exact (convolution_apply_rightKernel T U f _ (fun x => rfl)).symm

theorem pR_hecke_right (T : rightEssentiallyCompact μ) (h : Hecke.HeckeAlgebra μ) :
    (pR μ T ⟨heckeDistribution μ h, heckeDistribution_mem_right μ h⟩ : Distribution G) =
      rightHeckeConvolution μ (T : Distribution G) h := by
  ext f
  rw [pR_apply, rconv_heckeDistribution, rightHeckeConvolution_apply]

theorem pR_hecke_left (T : rightEssentiallyCompact μ) (h : Hecke.HeckeAlgebra μ) :
    (pR μ ⟨heckeDistribution μ h, heckeDistribution_mem_right μ h⟩ T : Distribution G) =
      leftHeckeConvolution μ h (T : Distribution G) := by
  ext f
  rw [pR_apply, leftHeckeConvolution_apply, leftHecke_eval]
  rfl

/-- Renard's right product satisfies the complete published right specification. -/
theorem pR_spec : RightProductSpecification μ (pR μ) := by
  refine ⟨⟨pR_assoc μ, ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact ⟨⟨dirac 1, dirac_mem_right μ⟩, rfl, fun T => ⟨pR_dirac_left μ T, pR_dirac_right μ T⟩⟩
  · intro T U
    exact ⟨⟨T, compactlySupported_le_right μ T.property⟩,
      ⟨U, compactlySupported_le_right μ U.property⟩, rfl, rfl, pR_compact μ T U⟩
  · intro T h
    exact ⟨⟨heckeDistribution μ h, heckeDistribution_mem_right μ h⟩, rfl,
      pR_hecke_right μ T h, pR_hecke_left μ T h⟩
  · intro T U f K hK hf
    have hr := (rightConvolveTest_eq_iff K hK f).mp hf
    obtain ⟨k, hk⟩ := exists_hecke_eq_right μ U.property
      (Hecke.HeckeAlgebra.normalizedIndicator μ K hK)
    refine ⟨k, hk, ?_⟩
    rw [pR_apply, rightHeckeConvolution_apply]
    congr 1
    ext x
    rw [rconv_apply, rightKernel_eq_convolution μ (U : Distribution G) K hK f hr
      (Hecke.HeckeAlgebra.toTestFunction μ k) hk]
  · intro T U h
    obtain ⟨k, hk⟩ := exists_hecke_eq_right μ U.property h
    exact ⟨k, hk, rightHecke_pRDist μ T U h k hk⟩

/-- Every product with the published right specification is Renard's right product. -/
theorem eq_pR (p : rightEssentiallyCompact μ →ₗ[ℂ]
      rightEssentiallyCompact μ →ₗ[ℂ] rightEssentiallyCompact μ)
    (hp : RightProductSpecification μ p) : p = pR μ := by
  apply LinearMap.ext
  intro T
  apply LinearMap.ext
  intro U
  apply Subtype.ext
  ext f
  obtain ⟨K, hK, -, hr⟩ := exists_biInvariant f
  obtain ⟨h, hh, hpf⟩ := hp.2.1 T U f K hK ((rightConvolveTest_eq_iff K hK f).mpr hr)
  rw [hpf, rightHeckeConvolution_apply, pR_apply]
  congr 1
  ext x
  rw [rconv_apply, rightKernel_eq_convolution μ (U : Distribution G) K hK f hr
    (Hecke.HeckeAlgebra.toTestFunction μ h) hh]

theorem right_existsUnique :
    ∃! p : rightEssentiallyCompact μ →ₗ[ℂ]
        rightEssentiallyCompact μ →ₗ[ℂ] rightEssentiallyCompact μ,
      RightProductSpecification μ p :=
  ⟨pR μ, pR_spec μ, fun p hp => eq_pR μ p hp⟩

end Langlands.HarmonicAnalysis.Distribution.RenardEssentialProducts

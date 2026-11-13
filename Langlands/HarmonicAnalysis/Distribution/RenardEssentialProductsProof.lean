import Langlands.HarmonicAnalysis.Distribution.RenardEssentialProductsRight
import Langlands.HarmonicAnalysis.Distribution.RenardEssentialProductsLeft

/-! # Renard II.3.13: proof of the essentially compact product statements -/

set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory

namespace Langlands.HarmonicAnalysis.Distribution.RenardEssentialProducts

universe uG

section TwoSided

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]

/-- For `T` left and `U` right essentially compact, `T_x U_y f(xy) = U_y T_x f(xy)`. -/
theorem two_sided_eval (T : leftEssentiallyCompact μ) (U : rightEssentiallyCompact μ)
    (f : SchwartzBruhat G) :
    (T : Distribution G) (rconv μ U f) = (U : Distribution G) (lconv μ T f) := by
  obtain ⟨K, hK, -, hr⟩ := exists_biInvariant f
  obtain ⟨k, hk⟩ := exists_testDensity_eq_right μ U.property
    (Hecke.HeckeAlgebra.normalizedIndicator μ K hK)
  have h1 : rconv μ U f =
      Hecke.TestFunction.convolution μ f (Hecke.TestFunction.inversion k) := by
    ext x
    rw [rconv_apply, rightKernel_eq_convolution μ (U : Distribution G) K hK f hr k hk]
  have h2 : (∫ y, k y * leftKernel (T : Distribution G) f y ∂μ) =
      testDensity μ k (lconv μ T f) := rfl
  rw [h1, rightHecke_eval, h2, hk, rightHeckeConvolution_apply,
    convolution_normalizedIndicator_of_right]
  intro k' hk' y
  rw [lconv_apply, lconv_apply, leftKernel_apply, leftKernel_apply]
  congr 1
  ext z
  simp [← mul_assoc, hr k' hk']

/-- The inclusion of the two-sided submodule into the right one. -/
def toR : essentiallyCompact μ →ₗ[ℂ] rightEssentiallyCompact μ :=
  Submodule.inclusion inf_le_left

/-- The inclusion of the two-sided submodule into the left one. -/
def toL : essentiallyCompact μ →ₗ[ℂ] leftEssentiallyCompact μ :=
  Submodule.inclusion inf_le_right

theorem pR_eq_pL (T U : essentiallyCompact μ) :
    (pR μ (toR μ T) (toR μ U) : Distribution G) = (pL μ (toL μ T) (toL μ U) : Distribution G) := by
  ext f
  rw [pR_apply, pL_apply]
  exact two_sided_eval μ (toL μ T) (toR μ U) f

theorem pEDist_mem (T U : essentiallyCompact μ) :
    (pR μ (toR μ T) (toR μ U) : Distribution G) ∈ essentiallyCompact μ := by
  refine Submodule.mem_inf.mpr ⟨(pR μ (toR μ T) (toR μ U)).property, ?_⟩
  rw [pR_eq_pL]
  exact (pL μ (toL μ T) (toL μ U)).property

/-- The product on the two-sided essentially compact submodule. -/
def pE : essentiallyCompact μ →ₗ[ℂ] essentiallyCompact μ →ₗ[ℂ] essentiallyCompact μ :=
  LinearMap.mk₂ ℂ (fun T U => ⟨(pR μ (toR μ T) (toR μ U) : Distribution G), pEDist_mem μ T U⟩)
    (fun T₁ T₂ U => Subtype.ext (LinearMap.ext fun f => rfl))
    (fun c T U => Subtype.ext (LinearMap.ext fun f => rfl))
    (fun T U₁ U₂ => Subtype.ext (LinearMap.ext fun f => by
      change (T : Distribution G) (rconv μ (toR μ (U₁ + U₂)) f) =
        (T : Distribution G) (rconv μ (toR μ U₁) f) +
          (T : Distribution G) (rconv μ (toR μ U₂) f)
      rw [map_add (toR μ), rconv_add, map_add]))
    (fun c T U => Subtype.ext (LinearMap.ext fun f => by
      change (T : Distribution G) (rconv μ (toR μ (c • U)) f) =
        c • (T : Distribution G) (rconv μ (toR μ U) f)
      rw [map_smul (toR μ), rconv_smul, map_smul]))

theorem coe_pE (T U : essentiallyCompact μ) :
    (pE μ T U : Distribution G) = (pR μ (toR μ T) (toR μ U) : Distribution G) := rfl

theorem toR_pE (T U : essentiallyCompact μ) :
    toR μ (pE μ T U) = pR μ (toR μ T) (toR μ U) := Subtype.ext rfl

theorem compact_mem_essentiallyCompact {T : Distribution G}
    (hT : T ∈ compactlySupported (X := G)) : T ∈ essentiallyCompact μ :=
  Submodule.mem_inf.mpr ⟨compactlySupported_le_right μ hT, compactlySupported_le_left μ hT⟩

theorem pE_algebraLaws : AlgebraLaws μ (essentiallyCompact μ) (pE μ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro T U V
    apply Subtype.ext
    rw [coe_pE, coe_pE, toR_pE, toR_pE, pR_assoc]
  · refine ⟨⟨dirac 1, compact_mem_essentiallyCompact μ (compactDirac (1 : G)).property⟩, rfl,
      fun T => ⟨?_, ?_⟩⟩
    · apply Subtype.ext
      rw [coe_pE]
      exact congrArg Subtype.val (pR_dirac_left μ (toR μ T))
    · apply Subtype.ext
      rw [coe_pE]
      exact congrArg Subtype.val (pR_dirac_right μ (toR μ T))
  · intro T U
    exact ⟨⟨T, compact_mem_essentiallyCompact μ T.property⟩,
      ⟨U, compact_mem_essentiallyCompact μ U.property⟩, rfl, rfl, pR_compact μ T U⟩
  · intro T h
    exact ⟨⟨heckeDistribution μ h, compact_mem_essentiallyCompact μ
        (RenardHaar.testDensity_compactlySupported μ (Hecke.HeckeAlgebra.toTestFunction μ h))⟩,
      rfl, pR_hecke_right μ (toR μ T) h, pR_hecke_left μ (toR μ T) h⟩

theorem pE_spec (pr : rightEssentiallyCompact μ →ₗ[ℂ]
      rightEssentiallyCompact μ →ₗ[ℂ] rightEssentiallyCompact μ)
    (pl : leftEssentiallyCompact μ →ₗ[ℂ]
      leftEssentiallyCompact μ →ₗ[ℂ] leftEssentiallyCompact μ)
    (hpr : RightProductSpecification μ pr) (hpl : LeftProductSpecification μ pl) :
    TwoSidedProductSpecification μ pr pl (pE μ) := by
  refine ⟨pE_algebraLaws μ, fun T U => ⟨toR μ T, toR μ U, toL μ T, toL μ U,
    rfl, rfl, rfl, rfl, ?_, ?_⟩⟩
  · rw [eq_pR μ pr hpr, coe_pE]
  · rw [eq_pL μ pl hpl, coe_pE, pR_eq_pL]

theorem eq_pE (pr : rightEssentiallyCompact μ →ₗ[ℂ]
      rightEssentiallyCompact μ →ₗ[ℂ] rightEssentiallyCompact μ)
    (pl : leftEssentiallyCompact μ →ₗ[ℂ]
      leftEssentiallyCompact μ →ₗ[ℂ] leftEssentiallyCompact μ)
    (hpr : RightProductSpecification μ pr)
    (p : essentiallyCompact μ →ₗ[ℂ] essentiallyCompact μ →ₗ[ℂ] essentiallyCompact μ)
    (hp : TwoSidedProductSpecification μ pr pl p) : p = pE μ := by
  apply LinearMap.ext
  intro T
  apply LinearMap.ext
  intro U
  obtain ⟨tr, ur, -, -, htr, hur, -, -, hpTU, -⟩ := hp.2 T U
  have etr : tr = toR μ T := Subtype.ext htr
  have eur : ur = toR μ U := Subtype.ext hur
  apply Subtype.ext
  rw [hpTU, etr, eur, eq_pR μ pr hpr, coe_pE]

end TwoSided

/-- Renard II.3.13: unique right and left products, and their common two-sided product. -/
theorem statements : Statements.{uG} := by
  intro G _ _ _ _ _ _ _ _ μ _
  refine ⟨right_existsUnique μ, left_existsUnique μ, ?_⟩
  intro pr pl hpr hpl
  exact ⟨pE μ, pE_spec μ pr pl hpr hpl, fun p hp => eq_pE μ pr pl hpr p hp⟩

end Langlands.HarmonicAnalysis.Distribution.RenardEssentialProducts

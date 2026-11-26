import Langlands.Automorphic.GroupSchemeFullAEL2ContinuousDensityStatement
import Langlands.Automorphic.GroupSchemeFullAEL2ContinuousCuspidality
import Langlands.Automorphic.GroupSchemeFullAEL2HermitianApproximationProof
import Langlands.Automorphic.GroupSchemeQuotientL2ContinuousRepresentativeProof
import Langlands.Global.AdelicConstantTermAverage
import Langlands.Representation.Unitary.IntegratedIsometricNaturalityProof

/-! # Density of continuous cuspidal classes by compact convolution -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Filter
open scoped CategoryTheory.MonObj CompactlySupported Topology

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme Langlands.Analysis

/-- Convolution with continuous compactly supported Hermitian weights keeps a closed
invariant subspace, converges strongly to the identity, and produces continuous
representatives whose mass-one parabolic periods vanish pointwise. -/
theorem groupSchemeFullAEL2ContinuousDensity :
    GroupSchemeFullAEL2ContinuousDensityStatement.{u} := by
  intro F _ _ G _ _ hPD hG T i hi _ I _ e hc _
  dsimp only
  intro P hP hPinv
  let μG : Measure (AdelicGroupPoints F G) := Measure.haar
  let μQ := positiveRationalQuotientHaarMeasure F G T i
  let S := fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc
  let π := fullAEL2CuspidalBoundedRightAction F G hPD hG T i hi I e hc
  let : μG.IsMulRightInvariant := ambientHaar_isMulRightInvariant F G T i hi I e hc
  let : μG.IsInvInvariant := ConstantTermAverage.isInvInvariant_of_isMulRightInvariant μG
  have hμ : μG.inv = μG := Measure.inv_eq_self μG
  obtain ⟨f, hf, hweight, _, _, _, _, htend, _, _, _⟩ :=
    groupSchemeFullAEL2HermitianApproximation F G hPD hG T i hi I e hc
  let w (n : ℕ) : C_c(AdelicGroupPoints F G, ℂ) :=
    ⟨⟨fun a => (f n a : ℂ), Complex.continuous_ofReal.comp (hweight n).1⟩,
      (hweight n).2.1.comp_left Complex.ofReal_zero⟩
  let hw (n : ℕ) : Integrable (w n) μG :=
    (w n).continuous.integrable_of_hasCompactSupport (w n).hasCompactSupport
  let B (n : ℕ) := fullAEL2CuspidalIntegratedAction F G hPD hG T i hi I e hc μG (w n) (hw n)
  have hB_tendsto (φ : S) : Tendsto (fun n => B n φ) atTop (𝓝 φ) := by
    convert htend φ using 1
    funext n
    change (∫ a, w n a • π a φ ∂μG) = ∫ a, (f n a : ℂ) • π a φ ∂μG.inv
    rw [hμ]
    rfl
  have hBP (n : ℕ) (φ : S) (hφ : φ ∈ P) : B n φ ∈ P :=
    (integratedIsometricNaturality μG π
      (norm_fullAEL2CuspidalBoundedRightAction F G hPD hG T i hi I e hc)
      (fullAEL2CuspidalOrbit_aestronglyMeasurable F G hPD hG T i hi I e hc μG)
      (w n) (hw n) P hP hPinv).choose φ hφ
  intro φ
  let ψ (n : ℕ) : P := ⟨B n φ.val, hBP n φ.val φ.property⟩
  have hψ : Tendsto ψ atTop (𝓝 φ) := by
    apply tendsto_subtype_rng.mpr
    exact hB_tendsto φ.val
  refine mem_closure_of_tendsto hψ ?_
  filter_upwards with n
  change (ψ n).val ∈ Set.range (positiveParabolicCuspidalL2ToFullAE F G hPD hG T i hi I e hc)
  obtain ⟨g, hg, hclass, _⟩ := groupSchemeQuotientL2ContinuousRepresentative F G T i hi I e hc
    (w n) (hw n) φ.val.val
  have hclass' : ((B n φ.val).val : PositiveRationalQuotient F G T i → ℂ) =ᵐ[μQ] g := by
    rwa [fullAEL2CuspidalIntegratedAction_val]
  let gC : C(PositiveRationalQuotient F G T i, ℂ) := ⟨g, hg⟩
  have hgCusp :=
    (groupSchemeFullAEL2ContinuousCuspidality F G hPD hG T i hi I e hc
      gC (B n φ.val).val hclass').mp (B n φ.val).property
  let gL2 : PositiveParabolicCuspidalL2Functions F G T i hPD hG
      (properParabolicQuotientMeasure F G hPD hG) μQ
      (haarQuotientMeasureRightInvariant F G T i hi I e hc) :=
    ⟨gC, hgCusp, MemLp.ae_eq hclass' (Lp.memLp _)⟩
  refine ⟨gL2, Subtype.ext (Lp.ext ?_)⟩
  exact (coeFn_positiveParabolicCuspidalL2ToLp F G T i hPD hG
    (properParabolicQuotientMeasure F G hPD hG) μQ
    (haarQuotientMeasureRightInvariant F G T i hi I e hc) gL2).trans hclass'.symm

end Langlands.Automorphic.GroupSchemeFunctions

import Langlands.Analysis.CompactPictureKernel
import Langlands.Analysis.ContinuousKernelHilbertSchmidt
import Langlands.Analysis.HilbertSchmidtIdealProof
import Langlands.Representation.Archimedean.RealPrincipalSeriesCompactModel

/-! # Integrated operators on the compact real Hilbert principal series -/

noncomputable section

open Filter MeasureTheory
open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealPrincipalSeriesHilbert

open Langlands.Analysis Langlands.Analysis.OperatorIdeals RealPrincipalSeriesDuality

attribute [local instance] measurableSpaceK borelSpaceK

variable {n : ℕ}

local notation "GL" => Langlands.GeneralLinear n ℝ
local notation "K" => unitaryCompact ℝ n
local notation "L2" => Lp ℂ 2 (haarK n)

local instance (d : ℕ) : SecondCountableTopology (Langlands.GeneralLinear d ℝ) :=
  Units.isOpenEmbedding_val.secondCountableTopology

local instance (d : ℕ) : SecondCountableTopology (unitaryCompact ℝ d) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology

variable [MeasurableSpace (Langlands.GeneralLinear n ℝ)] [BorelSpace (Langlands.GeneralLinear n ℝ)]
  (μ : Measure (Langlands.GeneralLinear n ℝ)) [IsFiniteMeasureOnCompacts μ]
  (a : Fin n → ℂ) (e : Fin n → Fin 2) (f : C(Langlands.GeneralLinear n ℝ, ℂ))

private def compactInclusion : C(K, GL) := ⟨Subtype.val, continuous_subtype_val⟩

/-- The kernel of the integrated real principal series, with the prescribed compact Haar measure. -/
def principalSeriesCompactKernel : C(K × K, ℂ) :=
  compactPictureKernel (unitaryCompact ℝ n).subtype continuous_subtype_val compactInclusion compactFactor
    (compactWeight a) f μ

private def translatedProfile (v : PrincipalSeries a e) (g : GL) : C(K, ℂ) :=
  compactRestriction a e (translation a e g v)

omit [MeasurableSpace (Langlands.GeneralLinear n ℝ)] [BorelSpace (Langlands.GeneralLinear n ℝ)] in
private theorem continuous_translatedProfile (v : PrincipalSeries a e) :
    Continuous (translatedProfile a e v) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : GL × K => v.1 ((p.2 : GL) * p.1))
  exact v.2.1.continuous.comp ((continuous_subtype_val.comp continuous_snd).mul continuous_fst)

private theorem integrable_weighted_hilbertOrbit (hf : HasCompactSupport f) (x : Hilbert a e) :
    Integrable (fun g => f g • representation a e g x) μ := by
  have hIn : Continuous (fun g : GL => (g, x)) := continuous_id.prodMk continuous_const
  have h := (isContinuousRepresentation a e).comp hIn
  have hC : Continuous (fun g => representation a e g x) := by
    simpa only [Function.comp_def] using h
  exact (f.continuous.smul hC).integrable_of_hasCompactSupport hf.smul_right

variable [SFinite μ] [μ.IsMulRightInvariant] [μ.IsMulLeftInvariant]

private theorem integral_translatedProfile (hf : HasCompactSupport f) (v : PrincipalSeries a e) :
    (∫ g, f g • translatedProfile a e v g ∂μ) =
      continuousKernelProfile (haarK n) (principalSeriesCompactKernel μ a f) (restrictToL2 a e v) := by
  have hInt : Integrable (fun g => f g • translatedProfile a e v g) μ :=
    (f.continuous.smul (continuous_translatedProfile a e v)).integrable_of_hasCompactSupport
      hf.smul_right
  ext k
  rw [ContinuousMap.integral_apply hInt k, continuousKernelProfile_apply]
  let P := compactRestriction a e v
  let κ := principalSeriesCompactKernel μ a f
  change (∫ g, f g * v.1 ((k : GL) * g) ∂μ) = ∫ z, κ (k, z) * restrictToL2 a e v z ∂haarK n
  have hshift := integral_mul_left_eq_self (μ := μ) (fun g => f ((k : GL)⁻¹ * g) * v.1 g) (k : GL)
  simp only [inv_mul_cancel_left] at hshift
  rw [hshift]
  trans ∫ g, f ((k : GL)⁻¹ * g) * (compactWeight a g * P (compactFactor g)) ∂μ
  · exact integral_congr_ae (Eventually.of_forall fun g =>
      congrArg (f ((k : GL)⁻¹ * g) * ·) (principalSeries_eq_compactProfile a e v g))
  · have h := integral_compactPictureKernel (unitaryCompact ℝ n).subtype continuous_subtype_val compactInclusion
      compactFactor (compactWeight a) f μ (haarK n) hf compactFactor_mul_compact
      (compactWeight_mul_compact a) P k
    change (∫ g, f ((k : GL)⁻¹ * g) * (compactWeight a g * P (compactFactor g)) ∂μ) =
      ∫ z, κ (k, z) * P z ∂haarK n at h
    rw [h]
    apply integral_congr_ae
    filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (μ := haarK n) (𝕜 := ℂ) P] with z hz
    change restrictToL2 a e v z = P z at hz
    rw [hz]

local notation "J" => Submodule.subtypeL (closureSubmodule a e)
local notation "B" => ContinuousMap.toLp (E := ℂ) 2 (haarK n) ℂ

set_option maxHeartbeats 600000 in
/-- The compact continuous kernel, evaluated in `L²`, agrees with the integrated operators
on the completed real principal series. -/
theorem integrated_eq_compactKernel (hf : HasCompactSupport f) (T : Hilbert a e →L[ℂ] Hilbert a e)
    (hT : ∀ x, T x = ∫ g, f g • representation a e g x ∂μ) :
    (J).comp T = ((B).comp (continuousKernelProfile (haarK n) (principalSeriesCompactKernel μ a f))).comp J := by
  let L := (B).comp (continuousKernelProfile (haarK n) (principalSeriesCompactKernel μ a f))
  apply ContinuousLinearMap.ext
  have he : ((J).comp T : Hilbert a e → L2) = (L.comp J : Hilbert a e → L2) := by
    apply Continuous.ext_on (denseRange_embed a e) ((J).comp T).continuous (L.comp J).continuous
    rintro _ ⟨v, rfl⟩
    let x := embed a e v
    let U : GL → Hilbert a e := fun g => f g • representation a e g x
    let P : GL → C(K, ℂ) := fun g => f g • translatedProfile a e v g
    have hU : Integrable U μ := integrable_weighted_hilbertOrbit μ a e f hf x
    have hP : Integrable P μ :=
      (f.continuous.smul (continuous_translatedProfile a e v)).integrable_of_hasCompactSupport hf.smul_right
    have heq (g : GL) : J (U g) = B (P g) := by
      change J (f g • representation a e g (embed a e v)) = B (f g • translatedProfile a e v g)
      rw [map_smul, map_smul, representation_embed]
      rfl
    change J (T x) = L (J x)
    calc
      _ = J (∫ g, U g ∂μ) := congrArg J (hT x)
      _ = ∫ g, J (U g) ∂μ := ((J).integral_comp_comm hU).symm
      _ = ∫ g, B (P g) ∂μ := integral_congr_ae (Eventually.of_forall heq)
      _ = B (∫ g, P g ∂μ) := (B).integral_comp_comm hP
      _ = _ := congrArg B (integral_translatedProfile μ a e f hf v)
  exact congrFun he

/-- Integration against a compactly supported continuous function gives a Hilbert–Schmidt
operator on the real compact-picture Hilbert completion. -/
theorem isHilbertSchmidt_integrated (hf : HasCompactSupport f) (T : Hilbert a e →L[ℂ] Hilbert a e)
    (hT : ∀ x, T x = ∫ g, f g • representation a e g x ∂μ) : IsHilbertSchmidt T := by
  have hS := isHilbertSchmidt_continuousKernelProfile (haarK n)
    (principalSeriesCompactKernel μ a f) (haarK n)
  have hJ : IsHilbertSchmidt ((J).comp T) := by
    rw [integrated_eq_compactKernel μ a e f hf T hT]
    exact isHilbertSchmidt_precomp _ J hS
  let P := (closureSubmodule a e).orthogonalProjectionOnto
  have he : P.comp ((J).comp T) = T := by
    apply ContinuousLinearMap.ext
    intro x
    exact (closureSubmodule a e).orthogonalProjectionOnto_mem_subspace_eq_self (T x)
  rw [← he]
  exact isHilbertSchmidt_postcomp _ P hJ

end Langlands.Archimedean.RealPrincipalSeriesHilbert

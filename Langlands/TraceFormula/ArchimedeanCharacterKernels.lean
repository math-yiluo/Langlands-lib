import Langlands.TraceFormula.ArchimedeanCompactPolynomialRankStatement
import Langlands.TraceFormula.ArchimedeanUnitaryCharacterSeparationStatement
import Langlands.Representation.Archimedean.GardingKernelOperations
import Langlands.Representation.Archimedean.UnitaryRegularization
import Langlands.Analysis.NormalizedAverageApproximation
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Prod

/-! # Integrated smooth tests for archimedean character separation -/

noncomputable section

open MeasureTheory Set
open scoped Classical Topology Manifold ContDiff Matrix.Norms.Operator InnerProductSpace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.TraceFormula.ArchimedeanUnitary

open Langlands.Global Langlands.Global.ArchimedeanGL Langlands.Archimedean

universe uF uE

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}

local notation "G" => InfiniteAdelicGL F n
local notation "M" => Langlands.Global.ArchimedeanMatrix F n
local notation "G'" => Langlands.Global.ArchimedeanGL F n
local notation "coords" => archimedeanGLCoordinates F n
local notation "Test" => SmoothCompactKernel F n

local instance modelCompleteSpace : CompleteSpace M :=
  inferInstanceAs (CompleteSpace (Fin n → Fin n → NumberField.mixedEmbedding.mixedSpace F))

private def modelKernel (f : Test) : smoothCompactKernels M G' :=
  ⟨f.val.val ∘ (coords).symm, f.val.property, f.property.comp_homeomorph (coords).symm.toHomeomorph⟩

private def pullKernel (f : smoothCompactKernels M G') : Test :=
  ⟨⟨f.val ∘ coords, by
    change ContMDiff 𝓘(ℝ, M) 𝓘(ℝ, ℂ) ∞ (fun g : G' => f.val (coords ((coords).symm g)))
    simpa only [ContinuousMulEquiv.apply_symm_apply] using f.property.1⟩,
    f.property.2.comp_homeomorph (coords).toHomeomorph⟩

/-- The test whose value at `g` is the original test's value at `a⁻¹ g`. -/
def leftTranslate (a : G) (f : Test) : Test :=
  pullKernel (gardingKernelLeft (A := M) (coords a) (modelKernel f))

@[simp]
theorem leftTranslate_apply (a : G) (f : Test) (g : G) :
    (leftTranslate a f).val.val g = f.val.val (a⁻¹ * g) := by
  change f.val.val ((coords).symm ((coords a)⁻¹ * coords g)) = _
  rw [map_mul, ← map_inv, ContinuousMulEquiv.symm_apply_apply, ContinuousMulEquiv.symm_apply_apply]

variable [MeasurableSpace (InfiniteAdelicGL F n)] [BorelSpace (InfiniteAdelicGL F n)]
variable (μ : Measure (InfiniteAdelicGL F n)) [μ.IsHaarMeasure]

local instance modelMeasurableSpace : MeasurableSpace G' := borel _
local instance modelBorelSpace : BorelSpace G' := ⟨rfl⟩

private instance modelLocallyCompactSpace : LocallyCompactSpace G' :=
  letI : LocallyCompactSpace M := inferInstanceAs
    (LocallyCompactSpace (Fin n → Fin n → NumberField.mixedEmbedding.mixedSpace F))
  (Units.isOpenEmbedding_val (R := M)).locallyCompactSpace

private instance modelSecondCountableTopology : SecondCountableTopology G' :=
  letI : SecondCountableTopology M := inferInstanceAs
    (SecondCountableTopology (Fin n → Fin n → NumberField.mixedEmbedding.mixedSpace F))
  (Units.isOpenEmbedding_val (R := M)).isEmbedding.secondCountableTopology

private instance originalSecondCountableTopology : SecondCountableTopology G :=
  infiniteGL_secondCountableTopology F n

/-- Smooth autocorrelation for the given left Haar measure. -/
def correlation (f : Test) : Test :=
  let ν : Measure G' := μ.map coords
  letI : ν.IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map μ coords
  pullKernel (gardingKernelConvolution (A := M) ν.inv
    (adjointGardingKernel (modelKernel f)) (modelKernel f))

@[simp]
theorem correlation_apply (f : Test) (g : G) :
    (correlation μ f).val.val g = ∫ a, star (f.val.val a) * f.val.val (a * g) ∂μ := by
  let e := (coords).toHomeomorph.toMeasurableEquiv
  change (∫ a : G', star (f.val.val ((coords).symm a⁻¹)) *
    f.val.val ((coords).symm (a⁻¹ * coords g)) ∂
      (Measure.map (MeasurableEquiv.inv G') (Measure.map e μ))) = _
  rw [integral_map_equiv (MeasurableEquiv.inv G'), integral_map_equiv e]
  simp only [MeasurableEquiv.inv_apply, inv_inv]
  apply integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  change star (f.val.val ((coords).symm (coords a))) *
    f.val.val ((coords).symm (coords a * coords g)) = _
  rw [← map_mul, ContinuousMulEquiv.symm_apply_apply, ContinuousMulEquiv.symm_apply_apply]

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {π : InfiniteAdelicGL F n →* (E →L[ℂ] E)}
  {A : SmoothCompactKernel F n → (E →L[ℂ] E)}

omit [NumberField F] [MeasurableSpace G] [BorelSpace G] [CompleteSpace E] in
private theorem continuous_orbit (hπ : IsUnitaryRepresentation π) (x : E) :
    Continuous (fun g : G => π g x) := by
  have hc : Continuous (fun p : G × E => π p.1 p.2) := hπ.1
  exact hc.comp (continuous_id.prodMk continuous_const)

private theorem kernel_integrable (f : Test) : Integrable f.val.val μ :=
  (ArchimedeanGL.continuous F n f.val).integrable_of_hasCompactSupport f.property

omit [CompleteSpace E] in
private theorem orbit_integrable (hπ : IsUnitaryRepresentation π) (f : Test) (x : E) :
    Integrable (fun a => f.val.val a • π a x) μ :=
  Continuous.integrable_of_hasCompactSupport
    ((ArchimedeanGL.continuous F n f.val).smul (continuous_orbit hπ x)) f.property.smul_right

/-- The bounded integrated operators depend complex linearly on the test. -/
def integratedLinearMap (hπ : IsUnitaryRepresentation π)
    (hA : ∀ f, IsIntegratedOperator μ π f (A f)) : Test →ₗ[ℂ] (E →L[ℂ] E) where
  toFun := A
  map_add' f g := ContinuousLinearMap.ext fun x => by
    change A (f + g) x = A f x + A g x
    rw [hA (f + g) x, hA f x, hA g x, ← integral_add
      (orbit_integrable μ hπ f x) (orbit_integrable μ hπ g x)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun a => add_smul _ _ _)
  map_smul' c f := ContinuousLinearMap.ext fun x => by
    change A (c • f) x = c • A f x
    rw [hA (c • f) x, hA f x, ← integral_smul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun a => mul_smul _ _ _)

/-- Left translation of the test multiplies the integrated operator on the left. -/
theorem integrated_leftTranslate (hπ : IsUnitaryRepresentation π)
    (hA : ∀ f, IsIntegratedOperator μ π f (A f)) (a : G) (f : Test) (x : E) :
    A (leftTranslate a f) x = π a (A f x) := by
  rw [hA, hA, ← (π a).integral_comp_comm (orbit_integrable μ hπ f x)]
  simp only [leftTranslate_apply]
  rw [← integral_mul_left_eq_self (fun g => f.val.val (a⁻¹ * g) • π g x) a]
  exact integral_congr_ae (Filter.Eventually.of_forall fun g => by
    dsimp only
    rw [inv_mul_cancel_left, map_mul, mul_apply_eq_comp, map_smul])

private theorem adjoint_integral (hπ : IsUnitaryRepresentation π)
    (hA : ∀ f, IsIntegratedOperator μ π f (A f)) (f : Test) (y : E) :
    (A f).adjoint y = ∫ a, star (f.val.val a) • π a⁻¹ y ∂μ := by
  apply ext_inner_right ℂ
  intro z
  let L : E →L[ℝ] ℂ := (RCLike.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.comp
    ((innerSL ℂ z).restrictScalars ℝ)
  have hL (v : E) : L v = inner ℂ v z := inner_conj_symm v z
  have hgi : Integrable (fun a => star (f.val.val a) • π a⁻¹ y) μ := by
    have hf : Continuous (fun a => star (f.val.val a)) := continuous_star.comp (ArchimedeanGL.continuous F n f.val)
    have hf' : HasCompactSupport (fun a => star (f.val.val a)) := f.property.comp_left (star_zero ℂ)
    exact Continuous.integrable_of_hasCompactSupport
      (hf.smul ((continuous_orbit hπ y).comp continuous_inv)) hf'.smul_right
  rw [ContinuousLinearMap.adjoint_inner_left, hA f z, ← hL]
  change (innerSL ℂ y) (∫ a, f.val.val a • π a z ∂μ) =
    L (∫ a, star (f.val.val a) • π a⁻¹ y ∂μ)
  rw [← (innerSL ℂ y).integral_comp_comm (orbit_integrable μ hπ f z),
    ← L.integral_comp_comm hgi]
  apply integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  have hi : π a (π a⁻¹ y) = y := by
    change (π a * π a⁻¹) y = y
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  have hinner : ⟪π a⁻¹ y, z⟫_ℂ = ⟪y, π a z⟫_ℂ := by
    simpa only [hi] using (hπ.2 a (π a⁻¹ y) z).symm
  simp only [innerSL_apply_apply, hL, inner_smul_right, inner_smul_left, starRingEnd_apply,
    star_star, hinner]

/-- Integrating the autocorrelation gives the positive square of the operator. -/
theorem integrated_correlation (hπ : IsUnitaryRepresentation π)
    (hA : ∀ f, IsIntegratedOperator μ π f (A f)) (f : Test) :
    A (correlation μ f) = (A f).adjoint.comp (A f) := by
  apply ContinuousLinearMap.ext
  intro x
  let k : G × G → ℂ := fun q => star (f.val.val q.1) * f.val.val (q.1 * q.2)
  have hcf : Integrable (fun a => star (f.val.val a)) μ :=
    (continuous_star.comp (ArchimedeanGL.continuous F n f.val)).integrable_of_hasCompactSupport
      (f.property.comp_left (star_zero ℂ))
  have hk : Integrable k (μ.prod μ) :=
    (measurePreserving_prod_mul μ μ).integrable_comp_of_integrable
      (hcf.mul_prod (kernel_integrable μ f))
  have hv : Integrable (fun q : G × G => k q • π q.2 x) (μ.prod μ) := by
    refine (hk.norm.mul_const ‖x‖).mono' (hk.aestronglyMeasurable.smul
      (continuous_orbit hπ x).aestronglyMeasurable.comp_snd) ?_
    filter_upwards [] with q
    simp only [norm_smul, norm_apply_of_preserves_inner π hπ.2, le_refl]
  have hini (a : G) : (∫ z, k (a, z) • π z x ∂μ) =
      star (f.val.val a) • π a⁻¹ (A f x) := by
    rw [← integral_mul_left_eq_self (fun z => k (a, z) • π z x) a⁻¹,
      hA f x, ← (π a⁻¹).integral_comp_comm (orbit_integrable μ hπ f x), ← integral_smul]
    apply integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [k, mul_inv_cancel_left, map_mul, mul_apply_eq_comp,
      map_smul, mul_smul]
  rw [hA (correlation μ f) x, ContinuousLinearMap.comp_apply, adjoint_integral μ hπ hA]
  calc
    (∫ g, (correlation μ f).val.val g • π g x ∂μ) =
        ∫ g, ∫ a, k (a, g) • π g x ∂μ ∂μ := by
      apply integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
      rw [correlation_apply]
      exact (integral_smul_const (fun a => k (a, g)) (π g x)).symm
    _ = ∫ a, ∫ g, k (a, g) • π g x ∂μ ∂μ := (integral_integral_swap hv).symm
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall hini)

/-- Every nonzero vector has a smooth compact test with a nonzero integrated image. -/
theorem exists_integrated_ne_zero (hπ : IsUnitaryRepresentation π)
    (hA : ∀ f, IsIntegratedOperator μ π f (A f)) {x : E} (hx : x ≠ 0) :
    ∃ f : Test, A f x ≠ 0 := by
  let ν : Measure G' := μ.map coords
  have : ν.IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map μ coords
  let U : Set G' := {g | ‖π ((coords).symm g) x - x‖ < ‖x‖ / 2}
  have hc : Continuous (fun g : G' => ‖π ((coords).symm g) x - x‖) :=
    (((continuous_orbit hπ x).comp (coords).symm.continuous).sub continuous_const).norm
  have hU : U ∈ 𝓝 (1 : G') := by
    apply (isOpen_lt hc continuous_const).mem_nhds
    change ‖π ((coords).symm 1) x - x‖ < ‖x‖ / 2
    simpa only [map_one, one_apply_eq_self, sub_self, norm_zero] using
      half_pos (norm_pos_iff.mpr hx)
  obtain ⟨φ, hs, hcomp, hsub, hmass, habs⟩ := exists_normalizedSmoothWeight (A := M) ν U hU
  let f : Test := pullKernel ⟨φ, hs, hcomp⟩
  have htranslate (g : G) (hg : f.val.val g ≠ 0) : ‖π g x - x‖ ≤ ‖x‖ / 2 := by
    have hp := hsub (subset_tsupport φ (Function.mem_support.mpr hg))
    exact le_of_lt (by simpa only [U, mem_ofPred_eq, ContinuousMulEquiv.symm_apply_apply] using hp)
  have hmass' : (∫ g, f.val.val g ∂μ) = 1 := by
    rw [← hmass]
    exact (integral_map_equiv (coords).toHomeomorph.toMeasurableEquiv φ).symm
  have habs' : (∫ g, ‖f.val.val g‖ ∂μ) = 1 := by
    rw [← habs]
    exact (integral_map_equiv (coords).toHomeomorph.toMeasurableEquiv (fun g => ‖φ g‖)).symm
  exact ⟨f, hA f x ▸ Langlands.Analysis.NormalizedAverage.integral_smul_ne_zero f.val.val
    (fun g => π g x) x hx
    (orbit_integrable μ hπ f x) (kernel_integrable μ f) hmass' habs' htranslate⟩

/-- A bounded intertwiner also intertwines all smooth integrated operators. -/
theorem map_integrated_apply {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : G →* (H →L[ℂ] H)} {B : Test → (H →L[ℂ] H)}
    (hπ : IsUnitaryRepresentation π) (hA : ∀ f, IsIntegratedOperator μ π f (A f))
    (hB : ∀ f, IsIntegratedOperator μ σ f (B f))
    (S : E →L[ℂ] H) (hS : ∀ g x, S (π g x) = σ g (S x)) (f : Test) (x : E) :
    S (A f x) = B f (S x) := by
  rw [hA f x, ← S.integral_comp_comm (orbit_integrable μ hπ f x), hB f (S x)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun g => by
    simp only [map_smul, hS])

end Langlands.TraceFormula.ArchimedeanUnitary

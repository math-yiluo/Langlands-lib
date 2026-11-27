import Langlands.Global.AdelicRightConvolutionEnveloping
import Langlands.Representation.Archimedean.GardingKernelDerivatives
import Langlands.Global.AdelicGroupPolish
import Langlands.Global.InfiniteAdelicModularCharacter

/-! # Archimedean test kernels at a fixed compact open adelic level -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Set
open scoped CategoryTheory.MonObj Manifold ContDiff ENNReal NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions Langlands.Archimedean
open Langlands.Geometry.Manifold AdelicGroupPoints InfiniteAdelicGroupPoints

variable {F : Type} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local notation "A" => AdelicGroupPoints F G
local notation "M" => InfiniteAdelicGroupPoints F G
local notation "B" => FiniteAdelicGroupPoints F G
local instance finitePointsMeasurableSpace : MeasurableSpace B := borel B
local instance finitePointsBorelSpace : BorelSpace B := ⟨rfl⟩

local notation "dm" => (Measure.haar : Measure M)
local notation "db" => (Measure.haar : Measure B)
local notation "dg" => (Measure.haar : Measure A)

/-- The finite level idempotent with Haar integral one. -/
def finiteLevelWeight (L : Subgroup B) : B → ℂ :=
  (L : Set B).indicator (fun _ => (((db).real (L : Set B))⁻¹ : ℝ))

private theorem finiteLevelWeight_continuous (L : Subgroup B) (hLo : IsOpen (L : Set B)) :
    Continuous (finiteLevelWeight L) :=
  IsClopen.continuous_indicator ⟨L.isClosed_of_isOpen hLo, hLo⟩ continuous_const

/-- The scalar connecting product Haar to the specified full adelic Haar measure. -/
def archimedeanKernelHaarScale : ℝ≥0 :=
  Measure.haarScalarFactor (((dm).prod db).map (split F G).symm) dg

/-- Lift a kernel on the infinite factor and attach the normalized finite level. -/
def liftArchimedeanKernel (L : Subgroup B) (h : M → ℂ) (x : A) : ℂ :=
  (archimedeanKernelHaarScale (F := F) (G := G) : ℂ) * h (infinite F G x) * finiteLevelWeight L (finite F G x)

variable {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)

local notation "I" => 𝓘(ℝ, smoothModel F d)

/-- Lifting a smooth compact kernel at a compact open finite level gives an adelic test. -/
theorem liftArchimedeanKernel_isTestFunction (L : Subgroup B) (hLo : IsOpen (L : Set B))
    (hLc : IsCompact (L : Set B)) (h : M → ℂ) (hsc : HasCompactSupport h) :
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    ContMDiff I 𝓘(ℝ, ℂ) ∞ h → IsAdelicTestFunction F G (liftArchimedeanKernel L h) := by
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hsmooth
  intro hsd
  have hcont := finiteLevelWeight_continuous L hLo
  have hr (l : B) (hl : l ∈ L) (b : B) : finiteLevelWeight L (b * l) = finiteLevelWeight L b := by
    by_cases hb : b ∈ L
    · rw [finiteLevelWeight, indicator_of_mem ((L.mul_mem_cancel_right hl).mpr hb) _, indicator_of_mem hb]
    · rw [finiteLevelWeight, indicator_of_notMem (fun hz => hb ((L.mul_mem_cancel_right hl).mp hz)) _,
        indicator_of_notMem hb]
  have hl (l : B) (hl : l ∈ L) (b : B) : finiteLevelWeight L (l * b) = finiteLevelWeight L b := by
    by_cases hb : b ∈ L
    · rw [finiteLevelWeight, indicator_of_mem ((L.mul_mem_cancel_left hl).mpr hb) _, indicator_of_mem hb]
    · rw [finiteLevelWeight, indicator_of_notMem (fun hz => hb ((L.mul_mem_cancel_left hl).mp hz)) _,
        indicator_of_notMem hb]
  refine ⟨⟨(continuous_const.mul (hsd.continuous.comp (infinite F G).continuous)).mul
    (hcont.comp (finite F G).continuous), ?_, L, hLo, ?_⟩, ?_, L, hLo, ?_⟩
  · intro b
    refine (isPlotSmooth_iff_contMDiff F G hsmooth _).mpr ?_
    let c : ℂ := (archimedeanKernelHaarScale (F := F) (G := G) : ℂ) * finiteLevelWeight L b
    let Z : ℂ →L[ℝ] ℂ := (ContinuousLinearMap.mul ℂ ℂ c).restrictScalars ℝ
    apply (Z.contDiff.contMDiff.comp hsd).congr
    intro a
    simp only [functionInfiniteSlice, liftArchimedeanKernel, infinite_pair, finite_pair]
    change _ = c * h a
    dsimp [c]
    ring
  · intro l h₁ x
    simp only [liftArchimedeanKernel, map_mul, infinite_ofFinite, finite_ofFinite, mul_one, hr l h₁]
  · have hS := (split F G).toHomeomorph.isCompact_preimage.mpr (hsc.prod hLc)
    apply HasCompactSupport.of_support_subset_isCompact hS
    intro x hx
    change infinite F G x ∈ tsupport h ∧ finite F G x ∈ L
    constructor
    · apply subset_tsupport
      intro h0
      exact hx (by simp [liftArchimedeanKernel, h0])
    · by_contra h0
      exact hx (by simp [liftArchimedeanKernel, finiteLevelWeight, indicator_of_notMem h0])
  · intro l h₁ x
    simp only [liftArchimedeanKernel, map_mul, infinite_ofFinite, finite_ofFinite, one_mul, hl l h₁]

/-- Integrating the lifted kernel on a fixed-level vector is integration over the infinite group. -/
theorem integral_liftArchimedeanKernel {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [CompleteSpace H] (π : A →* (H →L[ℂ] H)) (L : Subgroup B)
    (hLo : IsOpen (L : Set B)) (hLc : IsCompact (L : Set B))
    (h : M → ℂ) (hh : Continuous h) (hsc : HasCompactSupport h) (u : H)
    (hc : Continuous fun g : A => π g u) (hu : ∀ l ∈ L, π (ofFinite F G l) u = u) :
    (∫ x, liftArchimedeanKernel L h x • π x u ∂dg) = ∫ a, h a • π (ofInfinite F G a) u ∂dm := by
  let χ := finiteLevelWeight L
  let t := (db).real (L : Set B)
  have ht : 0 < t := ENNReal.toReal_pos
    (hLo.measure_pos db ⟨1, L.one_mem⟩).ne' hLc.measure_lt_top.ne
  have hχint : ∫ b, χ b ∂db = 1 := by
    rw [show χ = (L : Set B).indicator (fun _ => ((t⁻¹ : ℝ) : ℂ)) from rfl,
      integral_indicator_const _ hLo.measurableSet]
    change t • ((t⁻¹ : ℝ) : ℂ) = 1
    rw [Complex.real_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ ht.ne', Complex.ofReal_one]
  let c := archimedeanKernelHaarScale (F := F) (G := G)
  let e := split F G
  let ν := ((dm).prod db).map e.symm
  have : ν.IsHaarMeasure := e.symm.isHaarMeasure_map _
  have hν : ν = (c : ℝ≥0∞) • dg := Measure.isMulLeftInvariant_eq_smul ν dg
  let f (x : A) : H := (h (infinite F G x) * χ (finite F G x)) • π x u
  have hfull : (∫ x, liftArchimedeanKernel L h x • π x u ∂dg) = ∫ x, f x ∂ν := by
    rw [hν, integral_smul_measure, ← integral_smul]
    apply integral_congr_ae (ae_of_all _ fun x => ?_)
    rw [ENNReal.coe_toReal, ← Complex.coe_smul, smul_smul]
    simp only [liftArchimedeanKernel, c, χ, mul_assoc]
  let H₀ (p : M × B) := (h p.1 * χ p.2) • π (e.symm p) u
  have hHc : Continuous H₀ :=
    ((hh.comp continuous_fst).mul ((finiteLevelWeight_continuous L hLo).comp continuous_snd)).smul
      (hc.comp e.symm.continuous)
  have hHs : HasCompactSupport H₀ := by
    apply HasCompactSupport.of_support_subset_isCompact (hsc.prod hLc)
    rintro ⟨a, b⟩ hab
    change a ∈ tsupport h ∧ b ∈ (L : Set B)
    constructor
    · apply subset_tsupport
      intro hz
      exact hab (by simp [H₀, hz])
    · by_contra hn
      exact hab (by simp [H₀, χ, finiteLevelWeight, indicator_of_notMem hn])
  have hfiber (a : M) (b : B) : H₀ (a, b) = χ b • (h a • π (ofInfinite F G a) u) := by
    by_cases hb : b ∈ L
    · have heq : e.symm (a, b) = ofInfinite F G a * ofFinite F G b := by
        change pair F G a b = _
        rw [ofInfinite_eq_pair, ofFinite_eq_pair, AdelicGroupPoints.pair_mul, mul_one, one_mul]
      change (h a * χ b) • π (e.symm (a, b)) u = _
      rw [heq, map_mul, mul_apply_eq_comp, hu b hb, smul_smul, mul_comm (χ b)]
    · simp [H₀, χ, finiteLevelWeight, indicator_of_notMem hb]
  rw [hfull]
  change (∫ x, f x ∂(((dm).prod db).map e.symm.toHomeomorph.toMeasurableEquiv)) = _
  rw [integral_map_equiv]
  have hcmp : (fun p : M × B => f (e.symm.toHomeomorph.toMeasurableEquiv p)) = H₀ := by
    funext p
    change (h (infinite F G (e.symm p)) * χ (finite F G (e.symm p))) • π (e.symm p) u = _
    change (h (infinite F G (pair F G p.1 p.2)) * χ (finite F G (pair F G p.1 p.2))) • _ = _
    rw [infinite_pair, finite_pair]
  rw [hcmp]
  rw [integral_prod _ (hHc.integrable_of_hasCompactSupport hHs)]
  apply integral_congr_ae (ae_of_all _ fun a => ?_)
  simp_rw [hfiber]
  rw [integral_smul_const, hχint, one_smul]

/-- The actual adelic kernel derivative is the lift of the Gårding derivative. -/
theorem liftArchimedeanKernel_derivative (L : Subgroup B) (h : M → ℂ) :
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    letI := smoothLieGroup F G hsmooth
    ∀ (X : smoothModel F d), ContMDiff I 𝓘(ℝ, ℂ) ∞ h →
      rightConvolutionKernelDerivative hsmooth X (liftArchimedeanKernel L h) =
        liftArchimedeanKernel L (gardingKernelDerivative X h) := by
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hsmooth
  letI := smoothLieGroup F G hsmooth
  intro X hs
  funext x
  let g (t : M) := h (t⁻¹ * infinite F G x)
  let c : ℂ := archimedeanKernelHaarScale (F := F) (G := G)
  let b := finiteLevelWeight L (finite F G x)
  let A₀ : ℂ →L[ℝ] ℂ := (ContinuousLinearMap.mul ℂ ℂ (c * b)).restrictScalars ℝ
  have hfun : (fun t : M => liftArchimedeanKernel L h (ofInfinite F G t⁻¹ * x)) = A₀ ∘ g := by
    funext t
    simp only [liftArchimedeanKernel, map_mul, infinite_ofInfinite, finite_ofInfinite, one_mul]
    change c * g t * b = (c * b) * g t
    ring
  have hg : MDifferentiableAt I 𝓘(ℝ, ℂ) g 1 :=
    (hs.comp (contMDiff_id.inv.mul contMDiff_const)).mdifferentiableAt (by simp)
  unfold rightConvolutionKernelDerivative
  rw [hfun]
  change mfderiv I 𝓘(ℝ, ℂ) (A₀ ∘ g) 1 X = _
  rw [mfderiv_comp 1 A₀.differentiableAt.mdifferentiableAt hg, A₀.mfderiv_eq]
  change (c * b) * (gardingKernelDerivative X h (infinite F G x)) =
    c * (gardingKernelDerivative X h (infinite F G x)) * b
  ring

end Langlands.Global

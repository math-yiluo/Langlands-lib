import Langlands.Global.ArchimedeanCompactWeightedAverageStatement
import Langlands.Global.ArchimedeanSmoothDifferential
import Langlands.Analysis.CompactLinearParameterIntegralProof
import Langlands.Automorphic.RealDifferentialCovarianceProof

/-! # Actual smooth weighted averages over the standard compact subgroup -/

noncomputable section
universe u
open MeasureTheory Set Topology
open scoped Classical Manifold ContDiff Matrix.Norms.Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.ArchimedeanGL

namespace CompactWeightedAverage

variable {K : Type u} [Field K] [NumberField K] {n : ℕ}

/-- Right multiplication by the actual coordinate matrix of a compact element. -/
def rightMultiplicationMap (k : standardInfiniteCompact K n) :
    ArchimedeanMatrix K n →L[ℝ] ArchimedeanMatrix K n :=
  (ContinuousLinearMap.mul ℝ (ArchimedeanMatrix K n)).flip
    ((archimedeanGLCoordinates K n k.val : ArchimedeanGL K n) : ArchimedeanMatrix K n)

@[simp]
theorem rightMultiplicationMap_apply (k : standardInfiniteCompact K n)
    (x : ArchimedeanMatrix K n) :
    rightMultiplicationMap k x =
      x * (archimedeanGLCoordinates K n k.val : ArchimedeanMatrix K n) := rfl

theorem rightMultiplicationMap_units (k : standardInfiniteCompact K n)
    (g : ArchimedeanGL K n) :
    rightMultiplicationMap k (g : ArchimedeanMatrix K n) =
      ((g * archimedeanGLCoordinates K n k.val : ArchimedeanGL K n) :
        ArchimedeanMatrix K n) := rfl

theorem continuous_rightMultiplicationMap :
    Continuous (rightMultiplicationMap (K := K) (n := n)) :=
  (ContinuousLinearMap.mul ℝ (ArchimedeanMatrix K n)).flip.continuous.comp
    (Units.continuous_val.comp
      ((archimedeanGLCoordinates K n).continuous.comp continuous_subtype_val))

variable [MeasurableSpace (standardInfiniteCompact K n)]

/-- The scalar weighted compact right average of an actual smooth function. -/
def average (ν : Measure (standardInfiniteCompact K n))
    (w : C(standardInfiniteCompact K n, ℂ)) (f : SmoothFunctions K n)
    (x : InfiniteAdelicGL K n) : ℂ :=
  ∫ k : standardInfiniteCompact K n, w k * f.val (x * k.val) ∂ν

/-- An ambient matrix extension of the weighted average. -/
def ambientAverage (ν : Measure (standardInfiniteCompact K n))
    (w : C(standardInfiniteCompact K n, ℂ)) (f : SmoothFunctions K n)
    (x : ArchimedeanMatrix K n) : ℂ :=
  ∫ k : standardInfiniteCompact K n,
    w k * coordinateExtension K n f (rightMultiplicationMap k x) ∂ν

theorem ambientAverage_units (ν : Measure (standardInfiniteCompact K n))
    (w : C(standardInfiniteCompact K n, ℂ)) (f : SmoothFunctions K n)
    (g : ArchimedeanGL K n) :
    ambientAverage ν w f (g : ArchimedeanMatrix K n) =
      average ν w f ((archimedeanGLCoordinates K n).symm g) := by
  simp only [ambientAverage, average, rightMultiplicationMap_units,
    coordinateExtension_apply, map_mul, ContinuousMulEquiv.symm_apply_apply]

variable [BorelSpace (standardInfiniteCompact K n)]
variable (ν : Measure (standardInfiniteCompact K n)) [IsFiniteMeasure ν]
variable (w : C(standardInfiniteCompact K n, ℂ))

theorem average_integrable (f : SmoothFunctions K n) (x : InfiniteAdelicGL K n) :
    Integrable (fun k : standardInfiniteCompact K n => w k * f.val (x * k.val)) ν := by
  have h : Continuous (fun k : standardInfiniteCompact K n => w k * f.val (x * k.val)) :=
    w.continuous.mul ((continuous K n f).comp (continuous_const.mul continuous_subtype_val))
  exact h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Smoothness and the exact ambient first derivative of the scalar integral. -/
theorem ambientAverage_contDiffOn_hasFDerivAt (f : SmoothFunctions K n) :
    ContDiffOn ℝ ∞ (ambientAverage ν w f)
      (range (Units.val : ArchimedeanGL K n → ArchimedeanMatrix K n)) ∧
      ∀ g : ArchimedeanGL K n,
        HasFDerivAt (ambientAverage ν w f)
          (∫ k : standardInfiniteCompact K n,
            (w k) • ((fderiv ℝ (coordinateExtension K n f)
              (rightMultiplicationMap k (g : ArchimedeanMatrix K n))).comp
                (rightMultiplicationMap k)) ∂ν)
          (g : ArchimedeanMatrix K n) := by
  have hopen := (Units.isOpenEmbedding_val (R := ArchimedeanMatrix K n)).isOpen_range
  have hint := Langlands.Analysis.compactLinearParameterIntegral.{u, u, u}
    (standardInfiniteCompact K n) (ArchimedeanMatrix K n) (ArchimedeanMatrix K n) ν
    univ isCompact_univ
    (range (Units.val : ArchimedeanGL K n → ArchimedeanMatrix K n)) hopen
    (range (Units.val : ArchimedeanGL K n → ArchimedeanMatrix K n)) hopen
    w w.continuous rightMultiplicationMap continuous_rightMultiplicationMap
    (coordinateExtension K n f) (coordinateExtension_contDiffOn K n f)
    (by
      rintro k - _ ⟨g, rfl⟩
      exact ⟨_, (rightMultiplicationMap_units k g).symm⟩)
  simp only [Measure.restrict_univ] at hint
  exact ⟨hint.1, fun g => hint.2 _ ⟨g, rfl⟩⟩

/-- The scalar compact average is an actual smooth function. -/
theorem average_mem_smoothFunctions (f : SmoothFunctions K n) :
    average ν w f ∈ smoothFunctions K n := by
  change ContMDiff 𝓘(ℝ, ArchimedeanMatrix K n) 𝓘(ℝ, ℂ) ∞ _
  intro g
  have hopen := (Units.isOpenEmbedding_val (R := ArchimedeanMatrix K n)).isOpen_range
  have hat := (ambientAverage_contDiffOn_hasFDerivAt ν w f).1.contDiffAt
    (hopen.mem_nhds ⟨g, rfl⟩)
  have hcomp := hat.comp_contMDiffAt (Units.contMDiff_val (𝕜 := ℝ) (n := ∞) g)
  convert hcomp using 1
  funext x
  exact (ambientAverage_units ν w f x).symm

theorem ambientDerivative_integrable (f : SmoothFunctions K n) (g : ArchimedeanGL K n) :
    Integrable (fun k : standardInfiniteCompact K n =>
      (w k) • ((fderiv ℝ (coordinateExtension K n f)
        (rightMultiplicationMap k (g : ArchimedeanMatrix K n))).comp
          (rightMultiplicationMap k))) ν := by
  have hopen := (Units.isOpenEmbedding_val (R := ArchimedeanMatrix K n)).isOpen_range
  have hAt : ∀ k : standardInfiniteCompact K n, k ∈ univ →
      ∀ x ∈ range (Units.val : ArchimedeanGL K n → ArchimedeanMatrix K n),
        rightMultiplicationMap k x + (0 : ArchimedeanMatrix K n) ∈
          range (Units.val : ArchimedeanGL K n → ArchimedeanMatrix K n) := by
    rintro k - _ ⟨h, rfl⟩
    exact ⟨h * archimedeanGLCoordinates K n k.val, by simp⟩
  have hF := Langlands.Analysis.CompactLinearParameterIntegral.continuousOn_partialDeriv
    hopen w.continuous continuous_rightMultiplicationMap continuous_const
    (coordinateExtension_contDiffOn K n f) hAt
  have hi := (hF.comp (continuous_id.prodMk continuous_const).continuousOn
    (fun k hk => ⟨hk, ⟨g, rfl⟩⟩)).integrableOn_compact (μ := ν) isCompact_univ
  simpa only [IntegrableOn, add_zero, Measure.restrict_univ, Function.comp_def, id_eq] using hi

/-- The genuine smooth weighted average as a complex linear map. -/
def averageSmoothLM : SmoothFunctions K n →ₗ[ℂ] SmoothFunctions K n where
  toFun f := ⟨average ν w f, average_mem_smoothFunctions ν w f⟩
  map_add' f h := by
    apply Subtype.ext
    funext x
    change (∫ k : standardInfiniteCompact K n, w k * (f.val (x * k.val) + h.val (x * k.val)) ∂ν) = _
    simp_rw [mul_add]
    exact integral_add (average_integrable ν w f x) (average_integrable ν w h x)
  map_smul' c f := by
    apply Subtype.ext
    funext x
    change (∫ k : standardInfiniteCompact K n, w k * (c * f.val (x * k.val)) ∂ν) =
      c * (∫ k : standardInfiniteCompact K n, w k * f.val (x * k.val) ∂ν)
    simp_rw [← mul_assoc, mul_comm _ c, mul_assoc]
    exact integral_const_mul c _

@[simp]
theorem averageSmoothLM_apply (f : SmoothFunctions K n) (x : InfiniteAdelicGL K n) :
    (averageSmoothLM ν w f).val x = average ν w f x := rfl

/-- A genuine real Lie derivative passes through the scalar compact average. -/
theorem smoothDifferential_average (X : RealLieAlgebra K n)
    (f : SmoothFunctions K n) (x : InfiniteAdelicGL K n) :
    (smoothDifferential K n X (averageSmoothLM ν w f)).val x =
      ∫ k : standardInfiniteCompact K n,
        w k * (smoothDifferential K n X (smoothRightAction K n k.val f)).val x ∂ν := by
  rw [smoothDifferential_eq_of_extension K n X (averageSmoothLM ν w f)
    (ambientAverage ν w f) (ambientAverage_units ν w f)]
  rw [(ambientAverage_contDiffOn_hasFDerivAt ν w f).2
      (archimedeanGLCoordinates K n x) |>.fderiv,
    ContinuousLinearMap.integral_apply (ambientDerivative_integrable ν w f _)]
  apply integral_congr_ae
  filter_upwards [] with k
  simp only [smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
  congr 1
  have hext (g : ArchimedeanGL K n) :
      coordinateExtension K n f (rightMultiplicationMap k (g : ArchimedeanMatrix K n)) =
        (smoothRightAction K n k.val f).val ((archimedeanGLCoordinates K n).symm g) := by
    simp only [rightMultiplicationMap_units, coordinateExtension_apply, smoothRightAction_apply,
      map_mul, ContinuousMulEquiv.symm_apply_apply]
  rw [smoothDifferential_eq_of_extension K n X (smoothRightAction K n k.val f)
      (fun g => coordinateExtension K n f (rightMultiplicationMap k g)) hext]
  change _ = fderiv ℝ (coordinateExtension K n f ∘ rightMultiplicationMap k)
    (archimedeanGLCoordinates K n x : ArchimedeanMatrix K n) _
  have hdiff : DifferentiableAt ℝ (coordinateExtension K n f)
      (rightMultiplicationMap k (archimedeanGLCoordinates K n x : ArchimedeanMatrix K n)) := by
    exact (coordinateExtension_contDiffAt K n f
      (archimedeanGLCoordinates K n x * archimedeanGLCoordinates K n k.val)).differentiableAt
        (by simp)
  rw [fderiv_comp (archimedeanGLCoordinates K n x : ArchimedeanMatrix K n)
    hdiff (rightMultiplicationMap k).differentiableAt]
  simp only [ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply]

/-- The same actual average transported to the derivative topology carrier. -/
def averageLM : DerivativeSmoothFunctions K n →ₗ[ℂ] DerivativeSmoothFunctions K n :=
  (DerivativeSmoothFunctions.toSmooth K n).symm.toLinearMap.comp
    ((averageSmoothLM ν w).comp (DerivativeSmoothFunctions.toSmooth K n).toLinearMap)

@[simp]
theorem eval_averageLM (f : DerivativeSmoothFunctions K n) (x : InfiniteAdelicGL K n) :
    DerivativeSmoothFunctions.evalCLM K n x (averageLM ν w f) =
      ∫ k : standardInfiniteCompact K n,
        w k * DerivativeSmoothFunctions.evalCLM K n (x * k.val) f ∂ν := by
  simp only [DerivativeSmoothFunctions.evalCLM_apply, averageLM, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, averageSmoothLM, LinearMap.coe_mk,
    AddHom.coe_mk, average]

end CompactWeightedAverage
end Langlands.Global.ArchimedeanGL

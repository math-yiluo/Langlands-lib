import Langlands.Automorphic.TwoBlockConstantTermCovariance
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! # Differentiating two-block constant terms in the infinite factor -/

noncomputable section
universe u

open scoped Classical ContDiff Manifold Matrix.Norms.Operator Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global ArchimedeanGL ContinuousRationalFunctions MeasureTheory Set Topology

variable (F : Type u) [Field F] [NumberField F] (n : ℕ) {a b : ℕ} (h : a + b = n)

local notation "M" => ArchimedeanMatrix F n
local notation "G" => ArchimedeanGL F n
local notation "U" => Set.range (Units.val : G → M)
local notation "Q" => Matrix (Fin a) (Fin b) (AdeleQuotient F)

local instance constantTermSmoothRationalAddCommGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance constantTermSmoothContinuousAddCommGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance constantTermSmoothFiniteAddCommGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _

private def sliceIntegrand (f : FiniteSmoothRationalFunctions F n) (d : FiniteAdelicGL F n)
    (x : M) (q : Q) : ℂ :=
  constantTermIntegrand F n h f.val
    (AdelicGL.pair F n ((archimedeanGLCoordinates F n).symm ((unitsChart F n).symm x)) d) q

private theorem sliceIntegrand_apply_unit (f : FiniteSmoothRationalFunctions F n)
    (d : FiniteAdelicGL F n) (x : G) (q : Q) :
    sliceIntegrand F n h f d x.val q = constantTermIntegrand F n h f.val
      (AdelicGL.pair F n ((archimedeanGLCoordinates F n).symm x) d) q := by
  simp only [sliceIntegrand, unitsChart, IsOpenEmbedding.toOpenPartialHomeomorph_left_inv]

private def realDifferentiated (f : FiniteSmoothRationalFunctions F n) (V : M) :
    FiniteSmoothRationalFunctions F n :=
  finiteSmoothEnvelopingAction F n
    (envelopingGenerator F n (complexify F n ((realLieAlgebraToMatrix F n).symm V))) f

private def liftInfinite (q : Q) : G :=
  archimedeanGLCoordinates F n
    (AdelicGL.infinite F n (GeneralLinear.blockUnipotent h (matrixLift q)))

private def liftFinite (q : Q) : FiniteAdelicGL F n :=
  AdelicGL.finite F n (GeneralLinear.blockUnipotent h (matrixLift q))

private theorem sliceIntegrand_eq_evaluation (f : FiniteSmoothRationalFunctions F n)
    (d : FiniteAdelicGL F n) (x : G) (q : Q) :
    sliceIntegrand F n h f d x.val q =
      evaluate F n f.val (AdelicGL.pair F n
        ((archimedeanGLCoordinates F n).symm (liftInfinite F n h q * x))
        (liftFinite F n h q * d)) := by
  rw [sliceIntegrand_apply_unit, ← matrixQuotientMap_matrixLift q, constantTermIntegrand_mk,
    matrixQuotientMap_matrixLift]
  unfold liftInfinite liftFinite
  rw [map_mul, ContinuousMulEquiv.symm_apply_apply]
  conv_lhs => rw [← AdelicGL.pair_projections F n (GeneralLinear.blockUnipotent h (matrixLift q))]
  rw [AdelicGL.pair_mul]

private def liftedDerivative (f : FiniteSmoothRationalFunctions F n)
    (d : FiniteAdelicGL F n) (x : G) (q : Q) : M →L[ℝ] ℂ :=
  (fderiv ℝ (coordinateExtension F n (finiteSmoothSlice F n (liftFinite F n h q * d) f))
    ((liftInfinite F n h q * x : G) : M)).comp
      (ContinuousLinearMap.mul ℝ M (liftInfinite F n h q).val)

private theorem hasFDerivAt_sliceIntegrand_lifted (f : FiniteSmoothRationalFunctions F n)
    (d : FiniteAdelicGL F n) (x : G) (q : Q) :
    HasFDerivAt (fun y => sliceIntegrand F n h f d y q)
      (liftedDerivative F n h f d x q) x.val := by
  let A : M →L[ℝ] M := ContinuousLinearMap.mul ℝ M (liftInfinite F n h q).val
  let s := finiteSmoothSlice F n (liftFinite F n h q * d) f
  have hD : HasFDerivAt (coordinateExtension F n s)
      (fderiv ℝ (coordinateExtension F n s) ((liftInfinite F n h q * x : G) : M))
      (A x.val) :=
    ((coordinateExtension_contDiffAt F n s _).differentiableAt (by simp)).hasFDerivAt
  apply (hD.comp x.val A.hasFDerivAt).congr_of_eventuallyEq
  filter_upwards [Units.isOpenEmbedding_val.isOpen_range.mem_nhds (show x.val ∈ U from ⟨x, rfl⟩)]
    with y hy
  obtain ⟨z, rfl⟩ := hy
  rw [sliceIntegrand_eq_evaluation]
  change evaluate F n f.val (AdelicGL.pair F n _ _) =
    coordinateExtension F n s ((liftInfinite F n h q * z : G) : M)
  rw [coordinateExtension_apply]
  rfl

private theorem liftedDerivative_apply_mul (f : FiniteSmoothRationalFunctions F n)
    (d : FiniteAdelicGL F n) (x : G) (q : Q) (V : M) :
    liftedDerivative F n h f d x q (x.val * V) =
      sliceIntegrand F n h (realDifferentiated F n f V) d x.val q := by
  rw [sliceIntegrand_eq_evaluation]
  unfold realDifferentiated
  rw [evaluate_finiteSmoothEnvelopingAction_real_generator, ContinuousMulEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]
  change fderiv ℝ (coordinateExtension F n (finiteSmoothSlice F n (liftFinite F n h q * d) f))
      ((liftInfinite F n h q * x : G) : M) ((liftInfinite F n h q).val * (x.val * V)) = _
  rw [← mul_assoc]
  rfl

private def matrixBasis : Module.Basis (Fin (Module.finrank ℝ M)) ℝ M :=
  Module.finBasis ℝ M

private def rightMatrixCoordinate (x : G) (j : Fin (Module.finrank ℝ M)) : M →L[ℝ] ℝ :=
  ((matrixBasis F n).coord j).toContinuousLinearMap.comp
    (ContinuousLinearMap.mul ℝ M x⁻¹.val)

private def sliceIntegrandDerivative (f : FiniteSmoothRationalFunctions F n)
    (d : FiniteAdelicGL F n) (x : G) (q : Q) : M →L[ℝ] ℂ :=
  ∑ j, (rightMatrixCoordinate F n x j).smulRight
    (sliceIntegrand F n h (realDifferentiated F n f (matrixBasis F n j)) d x.val q)

private theorem sliceIntegrandDerivative_eq (f : FiniteSmoothRationalFunctions F n)
    (d : FiniteAdelicGL F n) (x : G) (q : Q) :
    sliceIntegrandDerivative F n h f d x q = liftedDerivative F n h f d x q := by
  ext V
  have hv : ∑ j, ((matrixBasis F n).coord j (x⁻¹.val * V)) • (x.val * matrixBasis F n j) = V := by
    calc
      _ = x.val * (∑ j, ((matrixBasis F n).coord j (x⁻¹.val * V)) • matrixBasis F n j) := by
        rw [Finset.mul_sum]
        simp only [Algebra.mul_smul_comm]
      _ = x.val * (x⁻¹.val * V) := by
        congr 1
        exact (matrixBasis F n).sum_repr _
      _ = V := by rw [← mul_assoc, Units.mul_inv, one_mul]
  have hsum :
      sliceIntegrandDerivative F n h f d x q V =
        ∑ j, ((matrixBasis F n).coord j (x⁻¹.val * V)) •
          liftedDerivative F n h f d x q (x.val * matrixBasis F n j) := by
    unfold sliceIntegrandDerivative
    simp only [sum_apply, ContinuousLinearMap.smulRight_apply, ← liftedDerivative_apply_mul]
    rfl
  rw [hsum]
  conv_rhs => rw [← hv, map_sum]
  simp only [map_smul]

set_option maxHeartbeats 600000 in
private theorem continuous_sliceIntegrand_on_units (f : FiniteSmoothRationalFunctions F n)
    (d : FiniteAdelicGL F n) :
    Continuous (fun p : Q × G => sliceIntegrand F n h f d p.2.val p.1) := by
  let g (x : G) : AdelicGL F n :=
    AdelicGL.pair F n ((archimedeanGLCoordinates F n).symm x) d
  have hg : Continuous g :=
    (AdelicGL.continuous_pair F n).comp
      ((archimedeanGLCoordinates F n).symm.continuous.prodMk continuous_const)
  have hp : Continuous (fun p : Q × G => (p.1, g p.2)) :=
    continuous_fst.prodMk (hg.comp continuous_snd)
  exact ((continuous_constantTermIntegrand_uncurry F n h f.val).comp hp).congr
    (fun p => (sliceIntegrand_apply_unit F n h f d p.2 p.1).symm)

private theorem continuous_sliceIntegrandDerivative (f : FiniteSmoothRationalFunctions F n)
    (d : FiniteAdelicGL F n) :
    Continuous (fun p : Q × G => sliceIntegrandDerivative F n h f d p.2 p.1) := by
  unfold sliceIntegrandDerivative
  apply continuous_finsetSum
  intro j _
  have hcoord : Continuous (fun p : Q × G => rightMatrixCoordinate F n p.2 j) :=
    continuous_const.clm_comp ((ContinuousLinearMap.mul ℝ M).continuous.comp
      (Units.continuous_val.comp (continuous_snd.inv)))
  exact ((ContinuousLinearMap.smulRightL ℝ M ℂ).continuous.comp hcoord).clm_apply
    (continuous_sliceIntegrand_on_units F n h _ d)

variable [CompactSpace (AdeleQuotient F)]

local instance constantTermSmoothMeasurableSpace : MeasurableSpace Q := borel _
local instance constantTermSmoothBorelSpace : BorelSpace Q := ⟨rfl⟩

/-- The constant term in a fixed finite slice, extended via the units chart. -/
def constantTermSliceExtension (f : FiniteSmoothRationalFunctions F n) (d : FiniteAdelicGL F n)
    (x : M) : ℂ :=
  ∫ q, sliceIntegrand F n h f d x q ∂matrixQuotientHaar F a b

theorem constantTermSliceExtension_apply_unit (f : FiniteSmoothRationalFunctions F n)
    (d : FiniteAdelicGL F n) (x : G) :
    constantTermSliceExtension F n h f d x.val =
      constantTerm F n h f.val (AdelicGL.pair F n ((archimedeanGLCoordinates F n).symm x) d) := by
  simp only [constantTermSliceExtension, constantTerm, sliceIntegrand_apply_unit]

private theorem integrable_sliceIntegrandDerivative (f : FiniteSmoothRationalFunctions F n)
    (d : FiniteAdelicGL F n) (x : G) :
    Integrable (fun q => sliceIntegrandDerivative F n h f d x q) (matrixQuotientHaar F a b) :=
  ((continuous_sliceIntegrandDerivative F n h f d).comp
    (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

set_option maxHeartbeats 800000 in
private theorem hasFDerivAt_constantTermSliceExtension (f : FiniteSmoothRationalFunctions F n)
    (d : FiniteAdelicGL F n) (x : G) :
    HasFDerivAt (constantTermSliceExtension F n h f d)
      (∫ q, sliceIntegrandDerivative F n h f d x q ∂matrixQuotientHaar F a b) x.val := by
  have hU : IsOpen U := Units.isOpenEmbedding_val.isOpen_range
  have hx : x.val ∈ U := ⟨x, rfl⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU x.val hx
  have hclosed : Metric.closedBall x.val (ε / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (half_lt_self hε)).trans hball
  have htarget : (unitsChart F n).target = U := by
    rw [unitsChart, IsOpenEmbedding.toOpenPartialHomeomorph_target]
  have hcompact : IsCompact ((unitsChart F n).symm '' Metric.closedBall x.val (ε / 2)) :=
    (isCompact_closedBall _ _).image_of_continuousOn
      ((unitsChart F n).continuousOn_symm.mono (htarget ▸ hclosed))
  obtain ⟨C, hC⟩ := ((isCompact_univ : IsCompact (univ : Set Q)).prod hcompact)
    |>.exists_bound_of_continuousOn (continuous_sliceIntegrandDerivative F n h f d).continuousOn
  let μ := matrixQuotientHaar F a b
  have hrep (y : G) : (unitsChart F n).symm y.val = y :=
    IsOpenEmbedding.toOpenPartialHomeomorph_left_inv _ _
  have hd := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := μ)
    (s := Metric.ball x.val (ε / 2))
    (F := sliceIntegrand F n h f d)
    (F' := fun y q => sliceIntegrandDerivative F n h f d ((unitsChart F n).symm y) q)
    (bound := fun _ => C) (Metric.ball_mem_nhds _ (half_pos hε)) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hrep] at hd
    exact hd
  · exact Filter.Eventually.of_forall fun y =>
      (continuous_constantTermIntegrand h f.val _).aestronglyMeasurable
  · exact integrable_constantTermIntegrand h f.val _
  · rw [hrep]
    exact (integrable_sliceIntegrandDerivative F n h f d x).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun q y hy =>
      hC (q, (unitsChart F n).symm y) ⟨mem_univ q, ⟨y, Metric.ball_subset_closedBall hy, rfl⟩⟩
  · exact integrable_const C
  · refine Filter.Eventually.of_forall fun q y hy => ?_
    obtain ⟨z, rfl⟩ := hclosed (Metric.ball_subset_closedBall hy)
    rw [hrep, sliceIntegrandDerivative_eq]
    exact hasFDerivAt_sliceIntegrand_lifted F n h f d z q

private theorem fderiv_constantTermSliceExtension_mul (f : FiniteSmoothRationalFunctions F n)
    (d : FiniteAdelicGL F n) (x : G) (V : M) :
    fderiv ℝ (constantTermSliceExtension F n h f d) x.val (x.val * V) =
      constantTermSliceExtension F n h (realDifferentiated F n f V) d x.val := by
  rw [(hasFDerivAt_constantTermSliceExtension F n h f d x).fderiv,
    ContinuousLinearMap.integral_apply (integrable_sliceIntegrandDerivative F n h f d x)]
  unfold constantTermSliceExtension
  simp only [sliceIntegrandDerivative_eq, liftedDerivative_apply_mul]

private theorem fderiv_constantTermSliceExtension (f : FiniteSmoothRationalFunctions F n)
    (d : FiniteAdelicGL F n) (x : G) (V : M) :
    fderiv ℝ (constantTermSliceExtension F n h f d) x.val V =
      ∑ j, rightMatrixCoordinate F n x j V •
        constantTermSliceExtension F n h (realDifferentiated F n f (matrixBasis F n j)) d x.val := by
  rw [(hasFDerivAt_constantTermSliceExtension F n h f d x).fderiv,
    ContinuousLinearMap.integral_apply (integrable_sliceIntegrandDerivative F n h f d x)]
  simp only [sliceIntegrandDerivative, sum_apply, ContinuousLinearMap.smulRight_apply]
  rw [integral_finsetSum]
  · simp only [integral_smul, constantTermSliceExtension]
  · intro j _
    simp only [sliceIntegrand_apply_unit]
    exact (integrable_constantTermIntegrand h _ _).smul _

omit [CompactSpace (AdeleQuotient F)] in
private theorem contDiffOn_rightMatrixCoordinate (j : Fin (Module.finrank ℝ M)) (V : M) :
    ContDiffOn ℝ ∞ (fun x => rightMatrixCoordinate F n ((unitsChart F n).symm x) j V) U := by
  have hchart : ContMDiffOn 𝓘(ℝ, M) 𝓘(ℝ, M) ∞
      (fun x : M => (unitsChart F n).symm x) U :=
    contMDiffOn_isOpenEmbedding_symm (I := 𝓘(ℝ, M)) Units.isOpenEmbedding_val
  have hinv : ContMDiff 𝓘(ℝ, M) 𝓘(ℝ, M) ∞ (fun x : G => x⁻¹.val) :=
    Units.contMDiff_val.comp (contMDiff_inv _ _)
  have hc := (hinv.comp_contMDiffOn hchart).contDiffOn
  change ContDiffOn ℝ ∞
    (fun x => ((matrixBasis F n).coord j).toContinuousLinearMap
      (((unitsChart F n).symm x)⁻¹.val * V)) U
  exact ((matrixBasis F n).coord j).toContinuousLinearMap.contDiff.comp_contDiffOn
    (hc.mul contDiffOn_const)

/-- The constant term of a finite-smooth function is smooth in every infinite slice. -/
theorem contDiffOn_constantTermSliceExtension (f : FiniteSmoothRationalFunctions F n)
    (d : FiniteAdelicGL F n) : ContDiffOn ℝ ∞ (constantTermSliceExtension F n h f d) U := by
  have hU : IsOpen U := Units.isOpenEmbedding_val.isOpen_range
  have hdiff (f' : FiniteSmoothRationalFunctions F n) :
      DifferentiableOn ℝ (constantTermSliceExtension F n h f' d) U := by
    rintro _ ⟨x, rfl⟩
    exact (hasFDerivAt_constantTermSliceExtension F n h f' d x).differentiableAt.differentiableWithinAt
  apply contDiffOn_infty.mpr
  intro k
  induction k generalizing f with
  | zero => exact contDiffOn_zero.mpr (hdiff f).continuousOn
  | succ k ih =>
    rw [Nat.cast_succ]
    refine contDiffOn_succ_of_fderiv_apply (hdiff f) (fun hk => by simp at hk) fun V => ?_
    let f' (j : Fin (Module.finrank ℝ M)) := realDifferentiated F n f (matrixBasis F n j)
    have hs : ContDiffOn ℝ k
        (fun x => ∑ j, rightMatrixCoordinate F n ((unitsChart F n).symm x) j V •
          constantTermSliceExtension F n h (f' j) d x) U :=
      ContDiffOn.sum fun j _ =>
        ((contDiffOn_rightMatrixCoordinate F n j V).of_le (by simp)).smul (ih (f' j))
    refine hs.congr ?_
    rintro _ ⟨x, rfl⟩
    rw [fderivWithin_of_isOpen hU ⟨x, rfl⟩, fderiv_constantTermSliceExtension,
      show (unitsChart F n).symm x.val = x from IsOpenEmbedding.toOpenPartialHomeomorph_left_inv _ _]

/-- The smooth infinite slice of a constant term at a fixed finite argument. -/
def smoothConstantTermSlice (f : FiniteSmoothRationalFunctions F n) (d : FiniteAdelicGL F n) :
    SmoothFunctions F n :=
  ⟨fun x => constantTerm F n h f.val (AdelicGL.pair F n x d), by
    intro x
    have hopen : IsOpen U := Units.isOpenEmbedding_val.isOpen_range
    have hx : x.val ∈ U := ⟨x, rfl⟩
    have hdiff := (contDiffOn_constantTermSliceExtension F n h f d).contDiffAt (hopen.mem_nhds hx)
    exact (hdiff.comp_contMDiffAt (Units.contMDiff_val (𝕜 := ℝ) (n := ∞) x)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y => (constantTermSliceExtension_apply_unit F n h f d y).symm)⟩

/-- The actual right Lie differential commutes with taking the constant term. -/
theorem smoothDifferential_smoothConstantTermSlice (f : FiniteSmoothRationalFunctions F n)
    (d : FiniteAdelicGL F n) (X : RealLieAlgebra F n) (g : InfiniteAdelicGL F n) :
    (smoothDifferential F n X (smoothConstantTermSlice F n h f d)).val g =
      constantTerm F n h (finiteSmoothEnvelopingAction F n
        (envelopingGenerator F n (complexify F n X)) f).val (AdelicGL.pair F n g d) := by
  rw [smoothDifferential_eq_of_extension F n X _ (constantTermSliceExtension F n h f d)
    (constantTermSliceExtension_apply_unit F n h f d),
    fderiv_constantTermSliceExtension_mul, constantTermSliceExtension_apply_unit]
  simp only [realDifferentiated, LinearEquiv.symm_apply_apply, ContinuousMulEquiv.symm_apply_apply]

end Langlands.Automorphic

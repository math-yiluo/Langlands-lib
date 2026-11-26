import Langlands.Global.RankinSelberg.RealGapAlternateConvergence
import Langlands.Global.RankinSelberg.RealUnequalConvergence
import Langlands.Global.RankinSelberg.RealAdjacentGodementHalfPlane
import Langlands.Global.RankinSelberg.UnfoldingGL

/-! # Independent rapid determinant weights on the real alternate gap kernel -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGapAlternateWeighted

open Langlands.Archimedean (unitaryCompact)
open Langlands.GeneralLinear (rankInclusion inverseTranspose continuous_inverseTranspose blockSum_apply_left
  blockSum_apply_left_right blockSum_apply_right_left blockSum_apply_right)
open Langlands.LocalFactor.Archimedean (RealBlock)
open Langlands.QuotientIntegration (leftQuotient_isOpenQuotientMap)
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open ArchimedeanLocal (RealQuotientMeasureData realNormalizedAbs realUnequalIntegrand)
open ArchimedeanMellinPair (RapidDecay)
open RealGapAlternateConvergence (alternateGapMeasure alternateGapNorm realGapAlternateConvergence)
open RealGapAlternateRetained (firstRetainedColumn lastRetainedInverseRow)
open RealGapColumnFourier (triangularFourier transposeColumn)
open RealGapLeadingSchwartz (leadingStack matrixDecay)
open RealGapTriangularChart (Outer retainedMatrix continuous_retainedMatrix)
open RealGapColumnFourier (continuous_psi)
open RealUnequalFamily (HasLeftCharacter)
open RealWhittakerTranslatedMellin (hasGaugeBound_of_mem_model)
open RealUnequalMellinReduction (quotientDetAbs continuous_quotientDetAbs)
open RealConvergenceAnalysis (norm_cexp_mul_ofReal)

local notation "G" => fun n => Langlands.GeneralLinear n ℝ
local notation "KU" => fun n => unitaryCompact ℝ n
local notation "U" => fun n => Langlands.GeneralLinear.upperUnipotent n ℝ
local notation "Q" => fun t => LeftUnipotentQuotient t ℝ
local notation "Mat" => fun m n => Matrix (Fin m) (Fin n) ℝ
local notation "Size" => fun t q => t + 1 + q + 1
local notation "YMat" => fun t q => Mat (q + 1) (t + 1)
local notation "Par" => fun t q => YMat t q × (Outer (t + 1) q × U (q + 1))
local notation "Coords" => fun t q => Q t × Par t q
local notation "δ" => fun g => realNormalizedAbs (Matrix.det (Units.val g))
local notation "ρ" => ArchimedeanLocal.translateFunction
local notation "H" => realMatrixHeight

local instance gapAlternateWeightedGLMeasurable (n : ℕ) : MeasurableSpace (G n) := borel _
local instance gapAlternateWeightedGLBorel (n : ℕ) : BorelSpace (G n) := ⟨rfl⟩
local instance gapAlternateWeightedGLSecondCountable (n : ℕ) : SecondCountableTopology (G n) :=
  (Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℝ) n).isInducing.secondCountableTopology
local instance gapAlternateWeightedUMeasurable (n : ℕ) : MeasurableSpace (U n) := borel _
local instance gapAlternateWeightedUBorel (n : ℕ) : BorelSpace (U n) := ⟨rfl⟩
local instance gapAlternateWeightedUSecondCountable (n : ℕ) : SecondCountableTopology (U n) :=
  (Langlands.GeneralLinear.upperEntryCoordinates (K := ℝ) n).secondCountableTopology
local instance gapAlternateWeightedMatrixBorel (m n : ℕ) : BorelSpace (Mat m n) :=
  inferInstanceAs (BorelSpace (Fin m → Fin n → ℝ))
local instance gapAlternateWeightedMatrixSecondCountable (m n : ℕ) : SecondCountableTopology (Mat m n) :=
  inferInstanceAs (SecondCountableTopology (Fin m → Fin n → ℝ))
local instance gapAlternateWeightedCompactSecondCountable (n : ℕ) : SecondCountableTopology (KU n) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance gapAlternateWeightedCompactOpens (n : ℕ) : OpensMeasurableSpace (KU n) :=
  Subtype.opensMeasurableSpace (fun g : G n => g ∈ unitaryCompact ℝ n)
local instance gapAlternateWeightedQSecondCountable (t : ℕ) : SecondCountableTopology (Q t) :=
  TopologicalSpace.Quotient.secondCountableTopology (leftQuotient_isOpenQuotientMap (U (t + 1))).isOpenMap
local instance gapAlternateWeightedQMeasurable (n : ℕ) : MeasurableSpace (Q n) := borel _
local instance gapAlternateWeightedQBorel (n : ℕ) : BorelSpace (Q n) := ⟨rfl⟩

/-- The matrix or its inverse transpose, according to the side of the leading Fourier comparison. -/
def leadingSide {n : ℕ} (dual : Bool) (g : G n) : G n := if dual then inverseTranspose n ℝ g else g

private theorem continuous_leadingSide (n : ℕ) (dual : Bool) : Continuous (leadingSide (n := n) dual) := by
  cases dual
  · exact continuous_id
  · exact continuous_inverseTranspose n ℝ

private theorem height_leadingSide {r : ℕ} (dual : Bool) (g : G (r + 1)) : H (leadingSide dual g) = H g := by
  cases dual
  · rfl
  · exact RealJacquet.realMatrixHeight_inverseTranspose g

private theorem padGL_eq_rankInclusion (k q : ℕ) (g : G k) :
    padGL (show k ≤ k + (q + 1) by omega) g = rankInclusion (q + 1) g := by
  apply Units.ext
  ext i j
  rw [Unfolding.padGL_apply]
  refine Fin.addCases (m := k) (n := q + 1) (fun i₀ => ?_) (fun i₁ => ?_) i <;>
    refine Fin.addCases (m := k) (n := q + 1) (fun j₀ => ?_) (fun j₁ => ?_) j
  · simp [rankInclusion, i₀.isLt, j₀.isLt]
  · simp [rankInclusion, i₀.isLt]
  · have hij : i₁.natAdd k ≠ j₀.castAdd (q + 1) := by
      intro h
      have he := congrArg Fin.val h
      change k + i₁.val = j₀.val at he
      omega
    simp [rankInclusion, hij]
  · simp [rankInclusion, Matrix.one_apply, Fin.natAdd_inj]

private theorem continuous_leadingStack {k q : ℕ} :
    Continuous (fun p : Mat k k × Mat (q + 1) k => leadingStack p.1 p.2) := by
  apply continuous_matrix
  intro i j
  refine Fin.addCases (m := k) (n := q + 1) (fun i₀ => ?_) (fun i₁ => ?_) i
  · simp only [leadingStack, Fin.append_left]
    exact ((continuous_apply j).comp (continuous_apply i₀ : Continuous (fun A : Mat k k => A i₀))).comp continuous_fst
  · simp only [leadingStack, Fin.append_right]
    exact ((continuous_apply j).comp (continuous_apply i₁ : Continuous (fun A : Mat (q + 1) k => A i₁))).comp continuous_snd

private theorem continuous_triangularFourier (k q : ℕ) (a : ℝˣ) (Ξ : Fin q → 𝓢((Fin (k + q + 1) → ℝ), ℂ)) :
    Continuous (fun p : G (k + q + 1) × U (q + 1) => triangularFourier k q a p.1 Ξ p.2) := by
  let A := G (k + q + 1) × U (q + 1)
  have hB : Continuous (fun p : A => ((p.1)⁻¹.val).transpose) :=
    (Units.continuous_val.comp (continuous_fst.inv : Continuous (fun p : A => p.1⁻¹))).matrix_transpose
  have hU : Continuous (fun p : A => p.2⁻¹.val) := continuous_subtype_val.comp (continuous_snd.inv)
  have hCol (j : Fin q) : Continuous (fun p : A => transposeColumn k q p.2⁻¹ j) := by
    apply continuous_pi
    intro i
    unfold transposeColumn
    split_ifs
    · exact continuous_const
    · exact (Langlands.GeneralLinear.entry (R := ℝ) j.castSucc _).continuous.comp hU
  unfold triangularFourier
  refine (continuous_finsetProd _ (fun j _ => ?_)).mul ?_
  · have hΨ : (RealGapColumnFourier.columnSchwartzFourier a (Ξ j) : (Fin (k + q + 1) → ℝ) → ℂ) =
        ArchimedeanLocal.realFourierTransform a (Ξ j) :=
      funext fun y => RealGapColumnFourier.columnSchwartzFourier_apply a (Ξ j) y
    rw [← hΨ]
    exact (RealGapColumnFourier.columnSchwartzFourier a (Ξ j)).continuous.comp (hB.matrix_mulVec (hCol j))
  · simp only [Whittaker.standardCharacter_apply]
    exact (continuous_psi a).comp (continuous_finsetSum _ fun j _ =>
      (Langlands.GeneralLinear.entry (R := ℝ) j.castSucc j.succ).continuous.comp
        (continuous_subtype_val.comp continuous_snd))

private theorem continuous_detPower {n : ℕ} (s : ℂ) :
    Continuous (fun g : G n => ArchimedeanLocal.detPower realNormalizedAbs g s) := by
  have hδ : Continuous (fun g : G n => δ g) := Units.continuous_val.matrix_det.abs
  have hlog := hδ.log fun g => abs_ne_zero.mpr g.det_ne_zero
  exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp hlog))

private theorem invariant_apply_out_mk {t : ℕ} {A : Type*} (f : G (t + 1) → A)
    (hf : ∀ u : U (t + 1), ∀ g, f (u.val * g) = f g) (g : G (t + 1)) :
    f (Quotient.mk (QuotientGroup.rightRel (U (t + 1))) g).out = f g :=
  congrArg (Langlands.QuotientIntegration.descend (U (t + 1)) f hf)
    (Quotient.out_eq (Quotient.mk (QuotientGroup.rightRel (U (t + 1))) g))

/-- The real unequal kernel evaluated at the class of any representative. -/
theorem ordinaryKernel_mk {r t : ℕ} (h : t < r) {a : ℝˣ} {W : G (r + 1) → ℂ}
    {W' : G (t + 1) → ℂ} (hW : HasLeftCharacter a W) (hW' : HasLeftCharacter (-a) W')
    (s : ℂ) (g : G (t + 1)) :
    realUnequalIntegrand h W W' s (Quotient.mk _ g) =
      W (padGL (Nat.succ_le_succ h.le) g) * W' g *
        ArchimedeanLocal.detPower realNormalizedAbs g (s - ((r - t : ℕ) : ℂ) / 2) := by
  refine invariant_apply_out_mk (fun g => W (padGL (Nat.succ_le_succ h.le) g) * W' g *
    ArchimedeanLocal.detPower realNormalizedAbs g (s - ((r - t : ℕ) : ℂ) / 2)) ?_ g
  intro u g
  have hp := RealUnequalConvergence.padGL_mem_upperUnipotent (Nat.succ_le_succ h.le) u.2
  have hdet : ArchimedeanLocal.detPower realNormalizedAbs (u.val * g) (s - ((r - t : ℕ) : ℂ) / 2) =
      ArchimedeanLocal.detPower realNormalizedAbs g (s - ((r - t : ℕ) : ℂ) / 2) := by
    have hu : u.val.val.det = 1 := by
      rw [Matrix.det_of_isUpperTriangular u.2.1, Finset.prod_eq_one fun i _ => u.2.2 i]
    simp only [ArchimedeanLocal.detPower, Units.val_mul, Matrix.det_mul, hu, one_mul]
  dsimp only
  rw [map_mul, hW _ hp, hW' _ u.2, hdet,
    RealUnequalConvergence.realWhittakerCharacter_padGL h (Nat.succ_le_succ h.le) a u.val]
  have hc := RealEqualConvergence.realWhittakerCharacter_mul_neg a u.val
  linear_combination (W (padGL (Nat.succ_le_succ h.le) g) * W' g *
    ArchimedeanLocal.detPower realNormalizedAbs g (s - ((r - t : ℕ) : ℂ) / 2)) * hc

/-- Right translates keep the left character. -/
theorem left_translate {r : ℕ} {a : ℝˣ} {W : G (r + 1) → ℂ} (hW : HasLeftCharacter a W)
    (x : G (r + 1)) : HasLeftCharacter a (ρ x W) := by
  intro u hu g
  change W ((u * g) * x) = _
  rw [mul_assoc, hW u hu]
  rfl

/-- Vectors of the uniform real Whittaker model have the left character. -/
theorem leftCharacter_of_mem {r : ℕ} {ds : List RealBlock} {a : ℝˣ} {W : G (r + 1) → ℂ}
    (hW : W ∈ realUniformWhittakerModel r ds a) : HasLeftCharacter a W :=
  fun u hu g => ((realUniformWhittakerRegularity r ds a W hW).1 []).1 u hu g

/-- Vectors of the uniform real Whittaker model are continuous. -/
theorem continuous_of_mem {r : ℕ} {ds : List RealBlock} {a : ℝˣ} {W : G (r + 1) → ℂ}
    (hW : W ∈ realUniformWhittakerModel r ds a) : Continuous W :=
  ((realUniformWhittakerRegularity r ds a W hW).1 []).2.1.continuous

private theorem gap_lt (t q : ℕ) : t < t + 1 + q := by omega

private theorem continuous_ordinaryProduct {t q : ℕ} {a : ℝˣ} (dual : Bool)
    {W : G (Size t q) → ℂ} {V : G (t + 1) → ℂ} (hWc : Continuous W) (hVc : Continuous V)
    (hWl : HasLeftCharacter (-a) W) (hVl : HasLeftCharacter (-(-a)) V) (s : ℂ) :
    Continuous (fun v : Coords t q => realUnequalIntegrand (gap_lt t q)
      (ρ ((retainedMatrix (t + 1) q v.2.2.1)⁻¹) W)
      (ρ (leadingSide dual v.2.2.1.1.1.1) V) s v.1) := by
  apply ((leftQuotient_isOpenQuotientMap (U (t + 1))).prodMap (IsOpenQuotientMap.id (X := Par t q))).isQuotientMap.continuous_iff.mpr
  change Continuous (fun v : G (t + 1) × Par t q => realUnequalIntegrand (gap_lt t q)
    (ρ ((retainedMatrix (t + 1) q v.2.2.1)⁻¹) W)
    (ρ (leadingSide dual v.2.2.1.1.1.1) V) s (Quotient.mk _ v.1))
  simp_rw [ordinaryKernel_mk _ (left_translate hWl _) (left_translate hVl _)]
  have hp : Continuous (fun v : G (t + 1) × Par t q => v.2.2.1) := by fun_prop
  have hz : Continuous (fun v : G (t + 1) × Par t q => v.2.2.1.1.1.1) := by fun_prop
  have hR := (continuous_retainedMatrix (t + 1) q).comp hp
  have hg : Continuous (fun v : G (t + 1) × Par t q => padGL (Nat.succ_le_succ (gap_lt t q).le) v.1 *
      (retainedMatrix (t + 1) q v.2.2.1)⁻¹) :=
    ((UnequalAnalytic.continuous_padGL (Nat.succ_le_succ (gap_lt t q).le)).comp continuous_fst).mul hR.inv
  have hv := continuous_fst.mul ((continuous_leadingSide (t + 1) dual).comp hz)
  exact ((hWc.comp hg).mul (hVc.comp hv)).mul
    ((continuous_detPower _).comp continuous_fst)

private def logScale {t q : ℕ} (c : ℝ) (p : Outer (t + 1) q) : ℝ := Real.exp (c * ∑ i, p.1.1.2 i)

private theorem continuous_logScale {t q : ℕ} (c : ℝ) : Continuous (logScale (t := t) (q := q) c) := by
  unfold logScale
  exact Real.continuous_exp.comp (continuous_const.mul (continuous_finsetSum _ fun i _ =>
    (continuous_apply i).comp (continuous_snd.comp (continuous_fst.comp continuous_fst))))

/-- On the unnormalized chart the two rapid weights may be rescaled by log-dependent scalar factors. -/
def weightedAlternateKernel {t q : ℕ} (dual : Bool) (a : ℝˣ) (Φ₀ : 𝓢(Mat (Size t q) (t + 1), ℂ))
    (Φ Ψ : 𝓢((Fin (Size t q) → ℝ), ℂ)) (Ξ : Fin q → 𝓢((Fin (Size t q) → ℝ), ℂ))
    (W : G (Size t q) → ℂ) (V : G (t + 1) → ℂ) (s : ℂ) (c₁ c₂ : ℝ)
    (f₁ f₂ : ℝ → ℂ) (w : Outer (t + 1) q → ℂ) (v : Coords t q) : ℂ :=
  let p := v.2.2.1
  let z := p.1.1.1
  let B := retainedMatrix (t + 1) q p
  Φ₀ ((leadingSide dual B).val * leadingStack z.val v.2.1) * Φ (firstRetainedColumn p) * Ψ (lastRetainedInverseRow p) *
    triangularFourier (t + 1) q a B Ξ v.2.2.2 *
    realUnequalIntegrand (gap_lt t q) (ρ B⁻¹ W) (ρ (leadingSide dual z) V) s v.1 *
    f₁ (logScale c₁ p * quotientDetAbs v.1) * f₂ (logScale c₂ p * δ z) * w p

set_option maxHeartbeats 850000 in
private theorem measurable_weightedAlternateKernel {t q : ℕ} (dual : Bool) (a : ℝˣ)
    (Φ₀ : 𝓢(Mat (Size t q) (t + 1), ℂ)) (Φ Ψ : 𝓢((Fin (Size t q) → ℝ), ℂ))
    (Ξ : Fin q → 𝓢((Fin (Size t q) → ℝ), ℂ))
    {W : G (Size t q) → ℂ} {V : G (t + 1) → ℂ} (hWc : Continuous W) (hVc : Continuous V)
    (hWl : HasLeftCharacter (-a) W) (hVl : HasLeftCharacter (-(-a)) V)
    (s : ℂ) (c₁ c₂ : ℝ) (f₁ f₂ : ℝ → ℂ) (w : Outer (t + 1) q → ℂ)
    (hf₁ : Measurable f₁) (hf₂ : Measurable f₂) (hw : Measurable w) :
    Measurable (weightedAlternateKernel dual a Φ₀ Φ Ψ Ξ W V s c₁ c₂ f₁ f₂ w) := by
  let p := fun v : Coords t q => v.2.2.1
  let z := fun v => (p v).1.1.1
  let B := fun v => retainedMatrix (t + 1) q (p v)
  have hp : Continuous p := by fun_prop
  have hz : Continuous z := by fun_prop
  have hB : Continuous B := (continuous_retainedMatrix (t + 1) q).comp hp
  have hY : Continuous (fun v : Coords t q => v.2.1) := continuous_fst.comp continuous_snd
  have hZ : Continuous (fun v : Coords t q => v.2.2.2) := by fun_prop
  have hLead := Φ₀.continuous.comp ((Units.continuous_val.comp ((continuous_leadingSide _ dual).comp hB)).matrix_mul
    (continuous_leadingStack.comp ((Units.continuous_val.comp hz).prodMk hY)))
  have hFirst : Continuous (fun v => firstRetainedColumn (p v)) := continuous_pi fun i =>
    (Langlands.GeneralLinear.entry (R := ℝ) i ((0 : Fin (q + 1)).natAdd (t + 1))).continuous.comp hB
  have hInv : Continuous (fun v => (B v)⁻¹) := hB.inv
  have hLast : Continuous (fun v => lastRetainedInverseRow (p v)) := continuous_pi fun i =>
    (Langlands.GeneralLinear.entry (R := ℝ) (Fin.last (t + 1 + q)) i).continuous.comp hInv
  have hTail := (continuous_triangularFourier (t + 1) q a Ξ).comp (hB.prodMk hZ)
  have hW := continuous_ordinaryProduct dual hWc hVc hWl hVl s
  have hδ : Continuous (fun v => δ (z v)) := (Units.continuous_val.comp hz).matrix_det.abs
  have h₁ := hf₁.comp (((continuous_logScale c₁).comp hp).mul (continuous_quotientDetAbs.comp continuous_fst)).measurable
  have h₂ := hf₂.comp (((continuous_logScale c₂).comp hp).mul hδ).measurable
  exact ((((((hLead.mul (Φ.continuous.comp hFirst)).mul (Ψ.continuous.comp hLast)).mul hTail).mul hW).measurable.mul h₁).mul h₂).mul
    (hw.comp hp.measurable)

private theorem norm_detFactor {n : ℕ} (g : G n) (s : ℂ) :
    ‖ArchimedeanLocal.detPower realNormalizedAbs g s‖ = δ g ^ s.re := by
  dsimp only
  have hp : 0 < δ g := abs_pos.mpr g.det_ne_zero
  rw [ArchimedeanLocal.detPower, norm_cexp_mul_ofReal, Real.rpow_def_of_pos hp, mul_comm]

private theorem scaled_rapid_bound {t q : ℕ} (f : ℝ → ℂ) (c pwr D : ℝ)
    (h : ∀ x, 0 < x → ‖f x‖ ≤ D * x ^ pwr) (p : Outer (t + 1) q) {x : ℝ} (hx : 0 < x) :
    ‖f (logScale c p * x)‖ ≤ D * x ^ pwr * Real.exp (|pwr * c| * ∑ i, |p.1.1.2 i|) := by
  let y := p.1.1.2
  have hy : |∑ i, y i| ≤ ∑ i, |y i| := Finset.abs_sum_le_sum_abs _ _
  have hD := RapidDecay.nonneg_const h
  have hc : 0 < logScale c p := Real.exp_pos _
  refine (h _ (mul_pos hc hx)).trans ?_
  rw [Real.mul_rpow hc.le hx.le, mul_comm (logScale c p ^ pwr) (x ^ pwr), ← mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hD (Real.rpow_nonneg hx.le _))
  unfold logScale
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  apply Real.exp_le_exp.mpr
  calc
    _ = (pwr * c) * ∑ i, y i := by dsimp only [y]; ring
    _ ≤ |pwr * c| * |∑ i, y i| := by rw [← abs_mul]; exact le_abs_self _
    _ ≤ _ := mul_le_mul_of_nonneg_left hy (abs_nonneg _)

/-- Independent rapid weights give joint convergence even after the scalar renormalization
of the leading variables. The remaining measured multiplier has the stated determinant and
logarithmic growth bound. -/
def RealGapAlternateWeightedStatement : Prop :=
  ∀ (t q : ℕ) (a : ℝˣ) (D : RealQuotientMeasureData t) (νY : Measure (YMat t q))
    (η₁ : Measure (G (t + 1))) (κ : Measure (KU (Size t q))),
    η₁.IsHaarMeasure → κ.IsHaarMeasure → SigmaFinite νY → ∀ l : ℕ, Integrable (matrixDecay l) νY →
    ∀ (dual : Bool) (ds es : List RealBlock) (W : G (Size t q) → ℂ) (V : G (t + 1) → ℂ),
      W ∈ realUniformWhittakerModel (t + 1 + q) ds (-a) → V ∈ realUniformWhittakerModel t es a →
    ∀ (Φ₀ : 𝓢(Mat (Size t q) (t + 1), ℂ))
      (Φ Ψ : 𝓢((Fin (Size t q) → ℝ), ℂ)) (Ξ : Fin q → 𝓢((Fin (Size t q) → ℝ), ℂ))
      (s : ℂ) (c₁ c₂ : ℝ) (f₁ f₂ : ℝ → ℂ) (w : Outer (t + 1) q → ℂ) (C β b : ℝ),
      0 ≤ C → 0 ≤ b → Measurable w → Measurable f₁ → Measurable f₂ → RapidDecay f₁ → RapidDecay f₂ →
      (∀ p, ‖w p‖ ≤ C * δ p.1.1.1 ^ β * Real.exp (b * ∑ i, |p.1.1.2 i|)) →
      Integrable (weightedAlternateKernel dual a Φ₀ Φ Ψ Ξ W V s c₁ c₂ f₁ f₂ w)
        (alternateGapMeasure t q a D νY η₁ κ)

set_option maxHeartbeats 1400000 in
/-- Each weight only needs a bound by one sufficiently large determinant power. -/
theorem realGapAlternatePowerBounds (t q : ℕ) (a : ℝˣ)
    (D : RealQuotientMeasureData t) (νY : Measure (YMat t q)) (η₁ : Measure (G (t + 1)))
    (κ : Measure (KU (Size t q))) (hη₁ : η₁.IsHaarMeasure)
    (hκ : κ.IsHaarMeasure) (hνY : SigmaFinite νY) (l : ℕ) (hY : Integrable (matrixDecay l) νY)
    (ds es : List RealBlock) (W : G (Size t q) → ℂ) (V : G (t + 1) → ℂ)
    (hWm : W ∈ realUniformWhittakerModel (t + 1 + q) ds (-a))
    (hVm : V ∈ realUniformWhittakerModel t es a) (s : ℂ) (β : ℝ) :
    ∃ u v : ℝ, ∀ (dual : Bool) (Φ₀ : 𝓢(Mat (Size t q) (t + 1), ℂ))
      (Φ Ψ : 𝓢((Fin (Size t q) → ℝ), ℂ)) (Ξ : Fin q → 𝓢((Fin (Size t q) → ℝ), ℂ))
      (c₁ c₂ : ℝ) (f₁ f₂ : ℝ → ℂ) (w : Outer (t + 1) q → ℂ) (C b p₁ p₂ C₁ C₂ : ℝ),
      0 ≤ C → 0 ≤ b → u ≤ p₁ → v ≤ p₂ → Measurable w → Measurable f₁ → Measurable f₂ →
      (∀ x, 0 < x → ‖f₁ x‖ ≤ C₁ * x ^ p₁) → (∀ x, 0 < x → ‖f₂ x‖ ≤ C₂ * x ^ p₂) →
      (∀ p, ‖w p‖ ≤ C * δ p.1.1.1 ^ β * Real.exp (b * ∑ i, |p.1.1.2 i|)) →
      Integrable (weightedAlternateKernel dual a Φ₀ Φ Ψ Ξ W V s c₁ c₂ f₁ f₂ w)
        (alternateGapMeasure t q a D νY η₁ κ) := by
  obtain ⟨u, v, hI⟩ := realGapAlternateConvergence t q a W V (hasGaugeBound_of_mem_model hWm)
    (hasGaugeBound_of_mem_model hVm) D νY η₁ κ hη₁ hκ hνY l hY
  let ω := (s - (((t + 1 + q) - t : ℕ) : ℂ) / 2).re
  refine ⟨u - ω, v - β, ?_⟩
  intro dual Φ₀ Φ Ψ Ξ c₁ c₂ f₁ f₂ w C b p₁ p₂ C₁ C₂ hC hb hp₁ hp₂ hw hm₁ hm₂ h₁ h₂ hwB
  have hVl : HasLeftCharacter (-(-a)) V := by
    rw [neg_neg]
    exact leftCharacter_of_mem hVm
  let F := weightedAlternateKernel dual a Φ₀ Φ Ψ Ξ W V s c₁ c₂ f₁ f₂ w
  have hF : Measurable F := measurable_weightedAlternateKernel dual a Φ₀ Φ Ψ Ξ
    (continuous_of_mem hWm) (continuous_of_mem hVm) (leftCharacter_of_mem hWm) hVl s c₁ c₂ f₁ f₂ w
    hm₁ hm₂ hw
  have hC₁ := RapidDecay.nonneg_const h₁
  have hC₂ := RapidDecay.nonneg_const h₂
  let d₁ := |p₁ * c₁|
  let d₂ := |p₂ * c₂|
  refine hI (ω + p₁) (p₂ + β) (b + d₁ + d₂) (by linarith) (by linarith) (by positivity)
    Φ₀ Φ Ψ Ξ (C₁ * C₂ * C) (by positivity)
    (fun p => leadingSide dual (retainedMatrix (t + 1) q p)) (fun p => leadingSide dual p.1.1.1)
    (fun p => (height_leadingSide dual _).le) (fun p => (height_leadingSide dual _).le) F hF.aestronglyMeasurable ?_
  intro x
  let p := x.2.2.1
  let g := x.1.out
  let z := p.1.1.1
  let B := retainedMatrix (t + 1) q p
  let S := ∑ i, |p.1.1.2 i|
  have hg : 0 < δ g := abs_pos.mpr g.det_ne_zero
  have hz : 0 < δ z := abs_pos.mpr z.det_ne_zero
  have hf₁' := scaled_rapid_bound f₁ c₁ p₁ C₁ h₁ p hg
  have hf₂' := scaled_rapid_bound f₂ c₂ p₂ C₂ h₂ p hz
  have hOrd : ‖realUnequalIntegrand (gap_lt t q) (ρ B⁻¹ W) (ρ (leadingSide dual z) V) s x.1‖ =
      ‖W (rankInclusion (q + 1) g * B⁻¹)‖ * ‖V (g * leadingSide dual z)‖ * δ g ^ ω := by
    unfold realUnequalIntegrand ArchimedeanLocal.unequalIntegrand ArchimedeanLocal.translateFunction
    simp only [norm_mul, norm_detFactor]
    exact congrArg (fun g₀ : G (Size t q) =>
      ‖W (g₀ * B⁻¹)‖ * ‖V (g * leadingSide dual z)‖ * δ g ^ ω)
      (padGL_eq_rankInclusion (t + 1) q g)
  have hw' := hwB p
  have hβ := Real.rpow_nonneg hz.le β
  have hω := Real.rpow_nonneg hg.le ω
  unfold F weightedAlternateKernel
  dsimp only
  simp only [norm_mul]
  calc
    _ ≤ ‖Φ₀ ((leadingSide dual B).val * leadingStack z.val x.2.1)‖ * ‖Φ (firstRetainedColumn p)‖ *
        ‖Ψ (lastRetainedInverseRow p)‖ * ‖triangularFourier (t + 1) q a B Ξ x.2.2.2‖ *
        (‖W (rankInclusion (q + 1) g * B⁻¹)‖ * ‖V (g * leadingSide dual z)‖ * δ g ^ ω) *
        (C₁ * δ g ^ p₁ * Real.exp (d₁ * S)) * (C₂ * δ z ^ p₂ * Real.exp (d₂ * S)) *
        (C * δ z ^ β * Real.exp (b * S)) := by
      gcongr
      · exact hOrd.le
      · exact hf₁'
    _ = _ := by
      dsimp only [alternateGapNorm, p, z, B, g, S]
      have hg' : δ x.1.out ^ ω * δ x.1.out ^ p₁ = δ x.1.out ^ (ω + p₁) := (Real.rpow_add hg _ _).symm
      have hz' : δ x.2.2.1.1.1.1 ^ p₂ * δ x.2.2.1.1.1.1 ^ β =
          δ x.2.2.1.1.1.1 ^ (p₂ + β) := (Real.rpow_add hz _ _).symm
      rw [show (b + d₁ + d₂) * (∑ i, |x.2.2.1.1.1.2 i|) =
        b * (∑ i, |x.2.2.1.1.1.2 i|) + d₁ * (∑ i, |x.2.2.1.1.1.2 i|) + d₂ * (∑ i, |x.2.2.1.1.1.2 i|) by ring,
        Real.exp_add, Real.exp_add, ← hg', ← hz']
      ring

theorem realGapAlternateWeighted : RealGapAlternateWeightedStatement := by
  intro t q a D νY η₁ κ hη₁ hκ hνY l hY dual ds es W V hWm hVm Φ₀ Φ Ψ Ξ s c₁ c₂ f₁ f₂ w C β b hC hb hw
    hm₁ hm₂ hf₁ hf₂ hwB
  obtain ⟨u, v, hI⟩ := realGapAlternatePowerBounds t q a D νY η₁ κ hη₁ hκ hνY l hY ds es W V hWm hVm s β
  obtain ⟨C₁, h₁⟩ := hf₁ u
  obtain ⟨C₂, h₂⟩ := hf₂ v
  exact hI dual Φ₀ Φ Ψ Ξ c₁ c₂ f₁ f₂ w C b u v C₁ C₂ hC hb le_rfl le_rfl hw hm₁ hm₂ h₁ h₂ hwB

end Langlands.Global.RankinSelbergGlobal.RealGapAlternateWeighted

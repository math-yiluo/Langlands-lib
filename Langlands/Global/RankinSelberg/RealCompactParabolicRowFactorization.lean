import Langlands.Global.RankinSelberg.RealCompactParabolicLeading
import Langlands.Global.RankinSelberg.RealUnequalLastRowDescent
import Langlands.Representation.Archimedean.SmoothVectorSubgroupFactorization

/-! # Compact rectangular row profiles for real Whittaker restrictions -/

noncomputable section

open MeasureTheory Set TopologicalSpace Matrix
open Langlands.Archimedean Langlands.Archimedean.DerivativeSmoothVectors
open Langlands.LocalFactor.Archimedean Langlands.HarmonicAnalysis Langlands.LinearLieGroup
open scoped ContDiff Distributions Manifold Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000

namespace Langlands.Global.RankinSelbergGlobal.RealParabolicCompactSection

open ArchimedeanLocal RealParabolicRowLift RealGodement
open RealUnequalLastRowDescent (colEntries colEntries_mul colUnip colUnip_mem character_colUnip padGL_mul_colUnip)

local notation "G" => fun n : ℕ => Langlands.GeneralLinear (n + 1) ℝ
local notation "Mat" => fun n : ℕ => Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ
local notation "N" => fun n : ℕ => Langlands.GeneralLinear.upperUnipotent (n + 1) ℝ
local notation "Rect" => fun m p : ℕ => Matrix (Fin (m + 1)) (Fin (p + 1)) ℝ
local notation "Test" => fun m p => 𝓓((⊤ : Opens (Rect m p)), ℂ)
local notation "last" => Langlands.RankinSelberg.lastRow

private def rectangleCoordinates (m p : ℕ) : (Fin ((m + 1) * (p + 1)) → ℝ) ≃L[ℝ] Rect m p :=
  ({ toFun := fun x i j => x (finProdFinEquiv (i, j))
     invFun := fun Y k => Y (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
     left_inv := by
       intro x
       funext k
       change x (finProdFinEquiv (finProdFinEquiv.symm k)) = x k
       rw [Equiv.apply_symm_apply]
     right_inv := by intro Y; ext i j; simp
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : _ ≃ₗ[ℝ] Rect m p).toContinuousLinearEquiv

private def columnDirections (n m p : ℕ) : Rect m p →ₗ[ℝ] Mat n where
  toFun Y := colEntries (r := n) (fun i => Y i 0)
  map_add' Y Z := by
    ext i j
    by_cases hi : i.val < m + 1 <;> by_cases hj : j.val = m + 1 <;>
      simp only [colEntries, hi, hj, ↓reduceDIte, ↓reduceIte, Matrix.add_apply, add_zero]
  map_smul' c Y := by
    ext i j
    by_cases hi : i.val < m + 1 <;> by_cases hj : j.val = m + 1 <;>
      simp only [colEntries, hi, hj, ↓reduceDIte, ↓reduceIte, Matrix.smul_apply,
        RingHom.id_apply, smul_zero]

private theorem columnDirections_mul (n m p : ℕ) (Y Z : Rect m p) :
    columnDirections n m p Y * columnDirections n m p Z = 0 := by
  change colEntries (r := n) (fun i => Y i 0) * colEntries (r := n) (fun i => Z i 0) = 0
  exact colEntries_mul _ _

private theorem exp_columnDirections {n m p : ℕ} (Y : Rect m p) :
    Langlands.LinearLieGroup.expUnit (Mat n) (columnDirections n m p Y) = colUnip (r := n) (fun i => Y i 0) := by
  apply Units.ext
  let A := columnDirections n m p Y
  change NormedSpace.exp A = 1 + A
  rw [NormedSpace.exp_eq_tsum ℝ]
  change (∑' k : ℕ, (k.factorial : ℝ)⁻¹ • A ^ k) = 1 + A
  rw [tsum_eq_sum (s := Finset.range 2) (fun k hk => ?_)]
  · simp [Finset.sum_range_succ]
  · have h : 2 ≤ k := by simpa only [Finset.mem_range, not_lt] using hk
    have hsq : A ^ 2 = 0 := by rw [pow_two, columnDirections_mul]
    rw [← Nat.add_sub_of_le h, pow_add, hsq, zero_mul, smul_zero]

private theorem compactRowProfile_integral {m p : ℕ} (a : ℝˣ) (φ : Test m p)
    (y : Fin (m + 1) → ℝ) :
    compactRowProfile a φ y = ∫ Y, φ Y * (realScaledCharacter (-a)).complex (∑ i, Y i 0 * y i)
      ∂Langlands.RankinSelberg.rectangularMeasure (realSelfDualMeasure a) (m + 1) (p + 1) := by
  rw [compactRowProfile, rowFourierProfile_apply, realRectangularSchwartzFourier_apply]
  unfold rectangularFourierIntegral
  have hμ : (realSelfDualMeasure (-a)).measure = (realSelfDualMeasure a).measure := by
    simp [realSelfDualMeasure]
  simp only [Langlands.RankinSelberg.rectangularMeasure, hμ]
  have hPair (Y : Rect m p) : rectangularPairing Y (boundaryFrequency y) = ∑ i, Y i 0 * y i := by
    unfold rectangularPairing
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single (0 : Fin (p + 1))]
    · simp [boundaryFrequency]
    · intro j _ hj
      simp [boundaryFrequency, hj]
    · simp
  simp_rw [hPair]
  rfl

/-- A restriction to a strictly smaller leading block is a finite sum of restrictions of genuine
smooth vectors with last-row profiles of compact rectangles at the opposite additive scale. -/
def RealCompactParabolicRowFactorizationStatement : Prop :=
  ∀ (n m p : ℕ) (h : m < n) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (R : G n →* (E →L[ℂ] E)),
    let I := 𝓘(ℝ, Mat n)
    let D := DerivativeSmoothVectors I R
    let act := representation I R
    IsContinuousRepresentation R → ∀ (a : ℝˣ) (L : D →L[ℂ] ℂ),
      (∀ (u : N n) (v : D), L (act u.val v) = realWhittakerCharacter (-a) u.val * L v) →
      ∀ v : D, ∃ (k : ℕ) (w : Fin k → D) (φ : Fin k → Test m p),
        ∀ g : G m, L (act (padGL (Nat.succ_le_succ h.le) g) v) =
          ∑ i, L (act (padGL (Nat.succ_le_succ h.le) g) (w i)) * compactRowProfile a (φ i) (last g)

set_option maxHeartbeats 900000 in
theorem realCompactParabolicRowFactorization : RealCompactParabolicRowFactorizationStatement := by
  intro n m p h E _ _ _ R I D act hR a L hL v
  let e := rectangleCoordinates m p
  let X := (columnDirections n m p).comp e.toLinearEquiv.toLinearMap
  have hX (t u : Fin ((m + 1) * (p + 1)) → ℝ) : Commute (X t) (X u) := by
    change columnDirections n m p (e t) * columnDirections n m p (e u) =
      columnDirections n m p (e u) * columnDirections n m p (e t)
    simp only [columnDirections_mul]
  obtain ⟨k, w, K, hK, hEq⟩ := smoothVectorCommutingDirectionsFactorization (Mat n) E R hR _ X hX v
  let ν := realSelfDualMeasure a
  let μ := Langlands.RankinSelberg.rectangularMeasure ν (m + 1) (p + 1)
  let η := (volume : Measure (Fin ((m + 1) * (p + 1)) → ℝ)).map e
  let : ν.measure.IsAddHaarMeasure := ν.isAddHaar
  let : SigmaFinite ν.measure := inferInstance
  let : (Measure.pi fun _ : Fin (p + 1) => ν.measure).IsAddHaarMeasure := inferInstance
  let : μ.IsAddHaarMeasure := inferInstance
  let : η.IsAddHaarMeasure := e.isAddHaarMeasure_map volume
  let c := Measure.addHaarScalarFactor η μ
  have hc : η = c • μ := Measure.isAddLeftInvariant_eq_smul η μ
  let φ (i : Fin k) : Test m p :=
    ⟨fun Y => (c : ℂ) * K i (e.symm Y), contDiff_const.mul ((hK i).1.comp e.symm.contDiff),
      ((hK i).2.comp_homeomorph e.symm.toHomeomorph).mul_left, subset_univ _⟩
  refine ⟨k, w, φ, fun g => ?_⟩
  let b := padGL (Nat.succ_le_succ h.le) g
  let Lg := L.comp (SmoothAction.derivativeAction I R b)
  have hCov (Y : Rect m p) (z : D) :
      Lg (act (Langlands.LinearLieGroup.expUnit (Mat n) (columnDirections n m p Y)) z) =
        (realScaledCharacter (-a)).complex (∑ i, Y i 0 * last g i) * Lg z := by
    change L (act b (act (Langlands.LinearLieGroup.expUnit (Mat n) (columnDirections n m p Y)) z)) = _
    rw [exp_columnDirections, ← Module.End.mul_apply, ← map_mul, padGL_mul_colUnip, map_mul,
      Module.End.mul_apply]
    let x : Fin (m + 1) → ℝ := fun i => Y i 0
    let u : N n := ⟨colUnip (r := n) (g.val *ᵥ x), colUnip_mem _⟩
    change L (act u.val (act b z)) = _
    rw [hL, show u.val = colUnip (g.val *ᵥ x) from rfl, character_colUnip _ _ (Nat.succ_lt_succ h),
      UnitaryAdditiveCharacter.complex_apply, realScaledCharacter_apply]
    have hx : (g.val *ᵥ x) (Fin.last m) = ∑ i, Y i 0 * last g i := by
      change (∑ i : Fin (m + 1), g.val (Fin.last m) i * Y i 0) = _
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [hx]
    rfl
  change Lg v = _
  rw [hEq Lg]
  refine Finset.sum_congr rfl fun i _ => ?_
  let F (Y : Rect m p) : ℂ := K i (e.symm Y) *
    ((realScaledCharacter (-a)).complex (∑ j, Y j 0 * last g j) * Lg (w i))
  have hF : Continuous F := ((hK i).1.continuous.comp e.symm.continuous).mul
    ((realScaledCharacter (-a)).continuous_complex.comp (continuous_finsetSum _ fun j _ =>
      (continuous_apply 0 |>.comp (continuous_apply j) : Continuous (fun Y : Rect m p => Y j 0)).mul
        continuous_const) |>.mul continuous_const)
  calc
    _ = ∫ Y, F Y ∂η := by
      rw [show η = Measure.map e volume from rfl, integral_map e.continuous.measurable.aemeasurable
        hF.aestronglyMeasurable]
      congr 1
      funext t
      change K i t * Lg (act (Langlands.LinearLieGroup.expUnit (Mat n) (columnDirections n m p (e t))) (w i)) = F (e t)
      rw [hCov]
      change K i t * _ = K i (e.symm (e t)) * _
      rw [e.symm_apply_apply]
    _ = ∫ Y, φ i Y * ((realScaledCharacter (-a)).complex (∑ j, Y j 0 * last g j) * Lg (w i)) ∂μ := by
      rw [hc, integral_smul_nnreal_measure]
      change (c : ℝ) • (∫ Y, F Y ∂μ) = _
      rw [← integral_smul]
      congr 1
      funext Y
      change (c : ℝ) • F Y = (c : ℂ) * K i (e.symm Y) *
        ((realScaledCharacter (-a)).complex (∑ j, Y j 0 * last g j) * Lg (w i))
      change (c : ℝ) • (K i (e.symm Y) * _) = (c : ℂ) * K i (e.symm Y) * _
      rw [Complex.real_smul, mul_assoc]
    _ = _ := by
      simp_rw [← mul_assoc]
      rw [integral_mul_const, ← compactRowProfile_integral, mul_comm]
      rfl

end Langlands.Global.RankinSelbergGlobal.RealParabolicCompactSection

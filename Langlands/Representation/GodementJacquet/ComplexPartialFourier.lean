import Langlands.Representation.GodementJacquet.ComplexFourierAffineSlice
import Langlands.Representation.GodementJacquet.ComplexFourierPartition
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Continuity and rapid decay for complex partial Fourier integrals -/

noncomputable section

open MeasureTheory Filter Topology
open scoped BigOperators Matrix.Norms.Elementwise

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet

open Langlands.HarmonicAnalysis
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal

section Bounds

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem exists_norm_schwartz_prod_le (Φ : SchwartzMap (E × F) ℂ) (p q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E, ∀ y : F,
      ‖Φ (x, y)‖ ≤ C / (1 + ‖x‖) ^ p * ((1 + ‖y‖) ^ q)⁻¹ := by
  let C := (2 : ℝ) ^ (p + q) * (Finset.Iic (p + q, 0)).sup
    (fun m => SchwartzMap.seminorm ℝ m.1 m.2) Φ
  refine ⟨C, by dsimp [C]; positivity, fun x y => ?_⟩
  rw [div_eq_mul_inv, mul_assoc, ← mul_inv, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  calc
    _ ≤ ‖Φ (x, y)‖ * ((1 + ‖(x, y)‖) ^ p * (1 + ‖(x, y)‖) ^ q) := by
      gcongr
      · exact norm_fst_le (x, y)
      · exact norm_snd_le (x, y)
    _ = (1 + ‖(x, y)‖) ^ (p + q) * ‖Φ (x, y)‖ := by rw [pow_add, mul_comm]
    _ ≤ C := by
      simpa only [C, norm_iteratedFDeriv_zero] using
        SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
          (m := (p + q, 0)) le_rfl le_rfl Φ (x, y)

variable [MeasurableSpace F]

omit [NormedSpace ℝ F] in
private theorem integrable_inv_pow (μ : Measure F) [μ.HasTemperateGrowth] :
    Integrable (fun y : F => ((1 + ‖y‖) ^ μ.integrablePower)⁻¹) μ := by
  simpa only [Real.rpow_neg (by positivity : 0 ≤ 1 + ‖(_ : F)‖), Real.rpow_natCast] using
    μ.integrable_pow_neg_integrablePower

private theorem exists_norm_integral_schwartz_mul_le (μ : Measure F) [μ.HasTemperateGrowth]
    (Φ : SchwartzMap (E × F) ℂ) (p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : E) (K : F → ℂ), (∀ y, ‖K y‖ ≤ 1) →
      ‖∫ y, Φ (x, y) * K y ∂μ‖ ≤ C / (1 + ‖x‖) ^ p := by
  obtain ⟨C, hC, hΦ⟩ := exists_norm_schwartz_prod_le Φ p μ.integrablePower
  let b : F → ℝ := fun y => ((1 + ‖y‖) ^ μ.integrablePower)⁻¹
  have hb : Integrable b μ := integrable_inv_pow μ
  refine ⟨C * ∫ y, b y ∂μ, mul_nonneg hC (integral_nonneg fun _ => by positivity),
    fun x K hK => ?_⟩
  calc
    _ ≤ ∫ y, (C / (1 + ‖x‖) ^ p) * b y ∂μ := by
      apply norm_integral_le_of_norm_le (hb.const_mul _)
      exact Eventually.of_forall fun y =>
        (by rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) (hK y) :
          ‖Φ (x, y) * K y‖ ≤ ‖Φ (x, y)‖).trans (hΦ x y)
    _ = _ := by rw [integral_const_mul]; ring

end Bounds

section CoordinateBlocks

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
local notation "A" => ι → ℂ
local notation "B" => κ → ℂ

/-- Fourier integration in the second block, holding the first block fixed. -/
def complexPartialFourier (a : ℂˣ) (Φ : A × B → ℂ) (p : A × B) : ℂ :=
  ∫ z, Φ (p.1, z) * traceCharacter a (complexCoordinatePair p.2 z)
    ∂complexCoordinateMeasure κ a

private theorem exists_schwartz_complexTwoBlockFourier (a : ℂˣ) (Φ : SchwartzMap (A × B) ℂ) :
    ∃ Ψ : SchwartzMap (A × B) ℂ, (Ψ : A × B → ℂ) = complexTwoBlockFourier a Φ := by
  let e := ContinuousLinearEquiv.sumPiEquivProdPi ℝ ι κ (fun _ => ℂ)
  let : (complexSelfDualMeasure a).measure.IsAddHaarMeasure := (complexSelfDualMeasure a).isAddHaar
  have he : MeasurePreserving e (complexCoordinateMeasure (ι ⊕ κ) a)
      ((complexCoordinateMeasure ι a).prod (complexCoordinateMeasure κ a)) :=
    measurePreserving_sumPiEquivProdPi (fun _ : ι ⊕ κ => (complexSelfDualMeasure a).measure)
  let H := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e Φ
  obtain ⟨H', hH'⟩ := exists_schwartz_complexCoordinateFourier a H
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm H', funext fun p => ?_⟩
  change H' (e.symm p) = _
  rw [congrFun hH' (e.symm p)]
  let g (q : A × B) := Φ q * traceCharacter a
    (complexCoordinatePair q.1 p.1 + complexCoordinatePair q.2 p.2)
  change (∫ x, H x * traceCharacter a (complexCoordinatePair x (e.symm p))
    ∂complexCoordinateMeasure (ι ⊕ κ) a) =
      ∫ q, g q ∂(complexCoordinateMeasure ι a).prod (complexCoordinateMeasure κ a)
  rw [← he.integral_comp e.toHomeomorph.measurableEmbedding g]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    change Φ (e x) * traceCharacter a (∑ i, x i * e.symm p i) =
      Φ (e x) * traceCharacter a ((∑ i, (e x).1 i * p.1 i) + ∑ i, (e x).2 i * p.2 i)
    rw [Fintype.sum_sum_type]
    rfl

/-- Dominated integration gives joint continuity of the partial transform. -/
theorem continuous_complexPartialFourier (a : ℂˣ) (Φ : SchwartzMap (A × B) ℂ) :
    Continuous (complexPartialFourier a Φ) := by
  let μ := complexCoordinateMeasure κ a
  let f (p : A × B) (z : B) := Φ (p.1, z) * traceCharacter a (complexCoordinatePair p.2 z)
  let b (z : B) := ((1 + ‖z‖) ^ μ.integrablePower)⁻¹
  obtain ⟨C, _, hC⟩ := exists_norm_schwartz_prod_le Φ 0 μ.integrablePower
  have hmeas (p : A × B) : AEStronglyMeasurable (f p) μ := by
    have hΦ : Continuous (fun z : B => Φ (p.1, z)) :=
      Φ.continuous.comp (continuous_const.prodMk continuous_id)
    have hcoord (i : κ) : Continuous (fun z : B => z i) := continuous_apply i
    have hpair : Continuous (complexCoordinatePair p.2) :=
      continuous_finsetSum _ fun i _ => continuous_const.mul (hcoord i)
    exact (hΦ.mul ((continuous_traceCharacter a).comp hpair)).aestronglyMeasurable
  have hcont (z : B) : Continuous (fun p => f p z) := by
    have hΦ : Continuous (fun p : A × B => Φ (p.1, z)) :=
      Φ.continuous.comp (continuous_fst.prodMk continuous_const)
    have hphase : Continuous (fun p : A × B => traceCharacter a (complexCoordinatePair p.2 z)) :=
      (continuous_traceCharacter a).comp ((continuous_complexCoordinatePair z).comp continuous_snd)
    exact hΦ.mul hphase
  have hbound (p : A × B) (z : B) : ‖f p z‖ ≤ C * b z := by
    simpa only [f, b, norm_mul, norm_traceCharacter, mul_one, pow_zero, div_one] using hC p.1 z
  apply continuous_iff_continuousAt.2
  intro p
  change Tendsto (fun q => ∫ z, f q z ∂μ) (𝓝 p) (𝓝 (∫ z, f p z ∂μ))
  exact tendsto_integral_filter_of_dominated_convergence (fun z => C * b z)
    (Eventually.of_forall hmeas) (Eventually.of_forall fun q => Eventually.of_forall (hbound q))
    ((integrable_inv_pow μ).const_mul C) (Eventually.of_forall fun z => (hcont z).continuousAt)

/-- First-block affine inversion gives the same partial integral as integration in
the original second block. It is enough to take the partial integral after swapping
the two blocks of the full transform. -/
private theorem complexPartialFourier_eq_integral_full (a : ℂˣ)
    (Φ : SchwartzMap (A × B) ℂ) (p : A × B) :
    complexPartialFourier a Φ p =
      ∫ w : A, complexTwoBlockFourier a Φ (w, p.2) *
        traceCharacter a (-complexCoordinatePair p.1 w) ∂complexCoordinateMeasure ι a := by
  let F := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.prodComm ℝ B A) Φ
  have h := (integral_complexTwoBlockFourier_affineSlice a F p.2 p.1).2.2
  have hFourier (w : A) :
      complexTwoBlockFourier a F (p.2, w) = complexTwoBlockFourier a Φ (w, p.2) := by
    let K (q : A × B) := Φ q * traceCharacter a
      (complexCoordinatePair q.1 w + complexCoordinatePair q.2 p.2)
    unfold complexTwoBlockFourier
    rw [← integral_prod_swap K]
    apply integral_congr_ae
    exact Eventually.of_forall fun q => by simp [F, K, add_comm]
  rw [show complexPartialFourier a Φ p =
      ∫ z : B, F (z, p.1) * traceCharacter a (complexCoordinatePair z p.2)
        ∂complexCoordinateMeasure κ a by
    apply integral_congr_ae
    exact Eventually.of_forall fun z => by
      simp [F, complexCoordinatePair, mul_comm (p.2 _ : ℂ)]] at *
  simpa only [hFourier] using h.symm

/-- The partial transform decays faster than any inverse polynomial in the
two blocks together. -/
theorem exists_norm_complexPartialFourier_le (a : ℂˣ) (Φ : SchwartzMap (A × B) ℂ) (p q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : A, ∀ y : B,
      ‖complexPartialFourier a Φ (x, y)‖ ≤ C / ((1 + ‖x‖) ^ p * (1 + ‖y‖) ^ q) := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_norm_integral_schwartz_mul_le
    (complexCoordinateMeasure κ a) Φ (p + q)
  obtain ⟨Ψ, hΨ⟩ := exists_schwartz_complexTwoBlockFourier a Φ
  let F := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.prodComm ℝ B A) Ψ
  obtain ⟨C₂, hC₂, h₂⟩ := exists_norm_integral_schwartz_mul_le
    (complexCoordinateMeasure ι a) F (p + q)
  refine ⟨max C₁ C₂, hC₁.trans (le_max_left _ _), fun x y => ?_⟩
  rcases le_total ‖y‖ ‖x‖ with hxy | hxy
  · calc
      _ ≤ C₁ / (1 + ‖x‖) ^ (p + q) :=
        h₁ x _ (fun _ => (norm_traceCharacter a _).le)
      _ ≤ _ := by
        rw [pow_add]
        gcongr
        exact le_max_left _ _
  · calc
      _ ≤ C₂ / (1 + ‖y‖) ^ (p + q) := by
        rw [complexPartialFourier_eq_integral_full, ← hΨ]
        exact h₂ y _ (fun _ => (norm_traceCharacter a _).le)
      _ ≤ _ := by
        rw [pow_add]
        gcongr
        exact le_max_right _ _

end CoordinateBlocks

section LastColumn

variable {m : ℕ}
local notation "I" => Fin m
local notation "M" => Matrix I I ℂ
local notation "Z" => I → ℂ
local notation "R" => Matrix I (Fin (m + 1)) ℂ

private def columnCoordinates : R ≃L[ℝ] ((I × I → ℂ) × Z) where
  toFun X := (complexRectangleUncurry m m (rectangularFirstColumns X), rectangularLastColumn X)
  invFun p := rectangularJoin ((complexRectangleUncurry m m).symm p.1) p.2
  left_inv X := by simp
  right_inv p := by simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := ((complexRectangleUncurry m m).continuous.comp
    continuous_rectangularFirstColumns).prodMk continuous_rectangularLastColumn
  continuous_invFun := continuous_rectangularJoin.comp
    (((complexRectangleUncurry m m).symm.continuous.comp continuous_fst).prodMk continuous_snd)

@[simp]
private theorem columnCoordinates_symm_uncurry (X : M) (z : Z) :
    columnCoordinates.symm (complexRectangleUncurry m m X, z) = rectangularJoin X z := by
  change rectangularJoin ((complexRectangleUncurry m m).symm (complexRectangleUncurry m m X)) z = _
  rw [ContinuousLinearEquiv.symm_apply_apply]

private theorem norm_complexRectangleUncurry_square (X : M) :
    ‖complexRectangleUncurry m m X‖ = ‖X‖ := by
  classical
  apply le_antisymm
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg X)).2
      (fun _ => Matrix.norm_entry_le_entrywise_sup_norm X)
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i =>
      (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j =>
        norm_le_pi_norm (complexRectangleUncurry m m X) (i, j)

/-- Fourier integration in the last column of a rectangular test. -/
def complexLastColumnFourier (a : ℂˣ) (Φ : R → ℂ) (X : M) (y : Z) : ℂ :=
  ∫ z, Φ (rectangularJoin X z) * traceCharacter a (complexCoordinatePair y z)
    ∂complexCoordinateMeasure I a

theorem continuous_complexLastColumnFourier (a : ℂˣ) (Φ : SchwartzMap R ℂ) :
    Continuous (fun p : M × Z => complexLastColumnFourier a Φ p.1 p.2) := by
  let F := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ columnCoordinates.symm Φ
  have h := (continuous_complexPartialFourier a F).comp
    (((complexRectangleUncurry m m).continuous.comp continuous_fst).prodMk continuous_snd)
  convert h using 1
  funext p
  change complexLastColumnFourier a Φ p.1 p.2 =
    complexPartialFourier a F (complexRectangleUncurry m m p.1, p.2)
  simp [complexLastColumnFourier, complexPartialFourier, F]

theorem exists_norm_complexLastColumnFourier_le (a : ℂˣ) (Φ : SchwartzMap R ℂ) (p q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (X : M) (y : Z),
      ‖complexLastColumnFourier a Φ X y‖ ≤ C / ((1 + ‖X‖) ^ p * (1 + ‖y‖) ^ q) := by
  let F := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ columnCoordinates.symm Φ
  obtain ⟨C, hC, hF⟩ := exists_norm_complexPartialFourier_le a F p q
  refine ⟨C, hC, fun X y => ?_⟩
  specialize hF (complexRectangleUncurry m m X) y
  rw [norm_complexRectangleUncurry_square] at hF
  simpa [complexLastColumnFourier, complexPartialFourier, F] using hF

end LastColumn

end Langlands.GodementJacquet

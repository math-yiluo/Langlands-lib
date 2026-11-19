import Langlands.Analysis.Local.QuotientInvariantComparison
import Langlands.Global.RankinSelberg.ComplexLocalWhittakerChangeCharacter
import Langlands.Global.RankinSelberg.UnipotentConjugationModulus
import Langlands.Group.GL.UpperBruhatCells
import Langlands.Representation.Archimedean.ComplexGramFormula

/-! # Logarithmic Iwasawa boxes on the complex left-unipotent quotient -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set TopologicalSpace
open scoped ENNReal NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexLocalConvergence

open ArchimedeanLocal Langlands.Archimedean Langlands.QuotientIntegration
open ComplexCharacterChange (diagonal_conj_mem)
open ComplexGramFormula (phaseUnit phaseUnit_val diagonalUnits_phaseUnit_mem)
open UnipotentConjugationModulus (conjugation conjugation_apply)
open Langlands.RankinSelberg (LeftUnipotentQuotient)

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

variable {r : ℕ}

local notation "I" => Fin (r + 1)
local notation "G" => Langlands.GeneralLinear (r + 1) ℂ
local notation "N" => GeneralLinear.upperUnipotent (r + 1) ℂ
local notation "Q" => LeftUnipotentQuotient r ℂ
local notation "K" => unitaryCompact ℂ (r + 1)
local notation "diag" => GeneralLinear.Iwasawa.diagonalUnits (F := ℂ)

private def expUnit (x : ℝ) : ℂˣ :=
  Units.mk0 (Real.exp x : ℂ) (by exact_mod_cast Real.exp_ne_zero x)

private theorem continuous_expUnit : Continuous expUnit := by
  apply Units.continuous_iff.mpr
  constructor
  · exact Complex.continuous_ofReal.comp Real.continuous_exp
  · change Continuous fun x : ℝ => (↑(Real.exp x) : ℂ)⁻¹
    have h : (fun x : ℝ => (↑(Real.exp x) : ℂ)⁻¹) = fun x => (↑(Real.exp (-x)) : ℂ) := by
      funext x
      rw [Real.exp_neg, Complex.ofReal_inv]
    rw [h]
    exact Complex.continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg)

/-- The positive diagonal with entries `exp (x i)`. -/
def expDiagonal (x : I → ℝ) : G :=
  diag fun i => expUnit (x i)

theorem expDiagonal_val (x : I → ℝ) :
    (expDiagonal x).val = Matrix.diagonal (fun i => (Real.exp (x i) : ℂ)) :=
  rfl

theorem continuous_expDiagonal : Continuous (expDiagonal : (I → ℝ) → G) :=
  (GeneralLinear.continuous_diagonalUnits _).comp
    (continuous_pi fun i => continuous_expUnit.comp (continuous_apply i))

theorem expDiagonal_add (x y : I → ℝ) :
    expDiagonal (x + y) = expDiagonal x * expDiagonal y := by
  unfold expDiagonal
  rw [← map_mul]
  congr 1
  funext i
  apply Units.ext
  change (Real.exp (x i + y i) : ℂ) = (Real.exp (x i) : ℂ) * (Real.exp (y i) : ℂ)
  rw [Real.exp_add, Complex.ofReal_mul]

private theorem expDiagonal_zero : expDiagonal (0 : I → ℝ) = 1 := by
  unfold expDiagonal
  have h : (fun i : I => expUnit ((0 : I → ℝ) i)) = 1 := by
    funext i
    apply Units.ext
    change (Real.exp 0 : ℂ) = 1
    simp
  rw [h, map_one]

theorem expDiagonal_neg (x : I → ℝ) : expDiagonal (-x) = (expDiagonal x)⁻¹ := by
  have h : expDiagonal x * expDiagonal (-x) = 1 := by
    rw [← expDiagonal_add, add_neg_cancel, expDiagonal_zero]
  calc
    _ = (expDiagonal x)⁻¹ * (expDiagonal x * expDiagonal (-x)) := (inv_mul_cancel_left _ _).symm
    _ = _ := by rw [h, mul_one]

private theorem diag_normalizes (d : I → ℂˣ) (g : G) :
    conjugation (diag d) g ∈ N ↔ g ∈ N := by
  rw [conjugation_apply]
  refine ⟨fun h => ?_, diagonal_conj_mem d g⟩
  have h' := diagonal_conj_mem d⁻¹ (diag d * g * (diag d)⁻¹) h
  rw [map_inv, inv_inv] at h'
  rwa [show (diag d)⁻¹ * (diag d * g * (diag d)⁻¹) * diag d = g by group] at h'

/-- A diagonal left translation on the quotient. -/
private def expShift (x : I → ℝ) : Q ≃ₜ Q :=
  (quotientAutomorphism N (conjugation (expDiagonal x)) (diag_normalizes _)).trans
    (rightTranslate N (expDiagonal x))

private theorem expShift_mk (x : I → ℝ) (g : G) :
    expShift x (Quotient.mk _ g) = Quotient.mk _ (expDiagonal x * g) := by
  change Quotient.mk _ (expDiagonal x * g * (expDiagonal x)⁻¹ * expDiagonal x) = _
  rw [inv_mul_cancel_right]

private theorem expShift_add (x y : I → ℝ) (q : Q) :
    expShift (x + y) q = expShift x (expShift y q) := by
  induction q using Quotient.inductionOn with
  | _ g => simp only [expShift_mk, expDiagonal_add, mul_assoc]

private theorem expShift_zero (q : Q) : expShift (0 : I → ℝ) q = q := by
  induction q using Quotient.inductionOn with
  | _ g => simp only [expShift_mk, expDiagonal_zero, one_mul]

private theorem expShift_symm (x : I → ℝ) (q : Q) :
    (expShift x).symm q = expShift (-x) q := by
  apply (expShift x).injective
  rw [Homeomorph.apply_symm_apply, ← expShift_add, add_neg_cancel, expShift_zero]

private theorem expShift_rightTranslate (x : I → ℝ) (g : G) (q : Q) :
    expShift x (rightTranslate N g q) = rightTranslate N g (expShift x q) := by
  induction q using Quotient.inductionOn with
  | _ q => simp only [rightTranslate_mk, expShift_mk, mul_assoc]

private theorem exists_measure_image_expShift (D : ComplexQuotientMeasureData r) (x : I → ℝ) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ S : Set Q, MeasurableSet S →
      D.measure (expShift x '' S) = (C : ℝ≥0∞) * D.measure S := by
  have hclosed : IsClosed (N : Set G) := GeneralLinear.UpperUnipotent.isClosed
  let : LocallyCompactSpace (Matrix I I ℂ) := inferInstanceAs (LocallyCompactSpace (I → I → ℂ))
  let : SecondCountableTopology (Matrix I I ℂ) := inferInstanceAs (SecondCountableTopology (I → I → ℂ))
  let : SecondCountableTopology (Matrix I I ℂ)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  let : PseudoMetrizableSpace (Matrix I I ℂ) := inferInstanceAs (PseudoMetrizableSpace (I → I → ℂ))
  let : PseudoMetrizableSpace (Matrix I I ℂ)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isInducing.pseudoMetrizableSpace
  let : LocallyCompactSpace G := inferInstance
  let : SecondCountableTopology G := Units.isInducing_embedProduct.secondCountableTopology
  let : PseudoMetrizableSpace G := Units.isInducing_embedProduct.pseudoMetrizableSpace
  let := leftQuotient_t2Space N hclosed
  let := leftQuotient_locallyCompactSpace N
  let := hclosed.locallyCompactSpace
  let : PseudoMetrizableSpace N := Topology.IsInducing.subtypeVal.pseudoMetrizableSpace
  let := D.unipotentHaar_isHaar
  let := D.unipotentHaar_rightInvariant
  let := Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure D.unipotentHaar
  let := D.compatible.regular
  let e := expShift x
  let μ := Measure.map e.symm D.measure
  let : μ.Regular := Regular.map e.symm
  have hm := e.symm.continuous.measurable
  have hne : μ ≠ 0 := by
    change D.measure.map e.symm ≠ 0
    rw [Ne, Measure.map_eq_zero_iff hm.aemeasurable]
    exact D.compatible.nonzero
  have hinv (g : G) : MeasurePreserving (rightTranslate N g) μ μ := by
    have hr := D.compatible.right_invariant g
    refine ⟨hr.measurable, ?_⟩
    have hcomm : rightTranslate N g ∘ e.symm = (e.symm : Q → Q) ∘ rightTranslate N g := by
      funext q
      simp only [Function.comp_apply, e, expShift_symm, expShift_rightTranslate]
    change Measure.map (rightTranslate N g) (Measure.map e.symm D.measure) = _
    rw [Measure.map_map hr.measurable hm, hcomm, ← Measure.map_map hm hr.measurable, hr.map_eq]
  obtain ⟨c, hc, hμ⟩ := exists_pos_smul_eq_of_rightInvariant_quotient N hclosed
    D.unipotentHaar μ D.measure hne D.compatible.nonzero hinv D.compatible.right_invariant
  refine ⟨c.toNNReal, Real.toNNReal_pos.mpr hc, fun S hS => ?_⟩
  change D.measure (e '' S) = _
  have hpre : e '' S = e.symm ⁻¹' S := e.toEquiv.image_eq_preimage_symm S
  rw [hpre, ← Measure.map_apply hm hS]
  change μ S = _
  rw [hμ, Measure.smul_apply, smul_eq_mul]
  rfl

/-- The quotient point with positive logarithmic diagonal `x` and right unitary factor `k`. -/
def torusPoint (x : I → ℝ) (k : K) : Q :=
  Quotient.mk _ (expDiagonal x * k.val)

private theorem continuous_torusPoint : Continuous fun p : (I → ℝ) × K => torusPoint p.1 p.2 :=
  continuous_quot_mk.comp
    ((continuous_expDiagonal.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd))

theorem torusPoint_surjective (q : Q) : ∃ (x : I → ℝ) (k : K), torusPoint x k = q := by
  induction q using Quotient.inductionOn with
  | _ g =>
    obtain ⟨d, u, k, hk, rfl⟩ :=
      ComplexDuality.exists_diagonalUnits_mul_upperUnipotent_mul_unitary g
    let x : I → ℝ := fun i => Real.log ‖(d i : ℂ)‖
    let phase : I → ℂˣ := fun i => phaseUnit (d i)
    let v : K := ⟨diag phase * k, mul_mem (diagonalUnits_phaseUnit_mem d) hk⟩
    have hdiag : expDiagonal x * diag phase = diag d := by
      unfold expDiagonal
      rw [← map_mul]
      congr 1
      funext i
      apply Units.ext
      change (Real.exp (Real.log ‖(d i : ℂ)‖) : ℂ) * (phaseUnit (d i) : ℂ) = d i
      have hd := norm_pos_iff.mpr (d i).ne_zero
      have hd' : (‖(d i : ℂ)‖ : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
      rw [Real.exp_log hd, phaseUnit_val]
      field_simp
    refine ⟨x, v, ?_⟩
    change Quotient.mk _ (expDiagonal x * (diag phase * k)) = Quotient.mk _ (diag d * u.val * k)
    rw [← mul_assoc, hdiag]
    apply Quotient.sound
    apply QuotientGroup.rightRel_apply.mpr
    change (diag d * u.val * k) * (diag d * k)⁻¹ ∈ N
    rw [show (diag d * u.val * k) * (diag d * k)⁻¹ = diag d * u.val * (diag d)⁻¹ by group]
    exact diagonal_conj_mem d _ u.property

/-- The image of the closed logarithmic box from `m` to `m+1`, with every right unitary
factor. The boxes may meet on their boundaries. -/
def torusBox (m : I → ℤ) : Set Q :=
  (fun p : (I → ℝ) × K => torusPoint p.1 p.2) ''
    ((Set.univ.pi fun i => Icc (m i : ℝ) ((m i : ℝ) + 1)) ×ˢ Set.univ)

theorem isCompact_torusBox (m : I → ℤ) : IsCompact (torusBox m) := by
  let := ComplexDuality.compactSpace_unitaryCompact (r + 1)
  exact ((isCompact_univ_pi fun _ => isCompact_Icc).prod isCompact_univ).image continuous_torusPoint

theorem iUnion_torusBox : (⋃ m : I → ℤ, torusBox m) = (Set.univ : Set Q) := by
  refine Set.eq_univ_of_forall fun q => ?_
  obtain ⟨x, k, rfl⟩ := torusPoint_surjective q
  refine Set.mem_iUnion.mpr ⟨fun i => ⌊x i⌋, ⟨(x, k), ⟨?_, Set.mem_univ _⟩, rfl⟩⟩
  intro i _
  exact ⟨Int.floor_le _, (Int.lt_floor_add_one _).le⟩

private theorem torusBox_eq_shift (m : I → ℤ) :
    torusBox m = expShift (fun i => m i) '' torusBox 0 := by
  ext q
  constructor
  · rintro ⟨⟨x, k⟩, ⟨hx, _⟩, rfl⟩
    let y : I → ℝ := fun i => x i - m i
    refine ⟨torusPoint y k, ⟨(y, k), ⟨?_, Set.mem_univ _⟩, rfl⟩, ?_⟩
    · intro i hi
      have h := hx i hi
      change (m i : ℝ) ≤ x i ∧ x i ≤ (m i : ℝ) + 1 at h
      change ((0 : I → ℤ) i : ℝ) ≤ y i ∧ y i ≤ ((0 : I → ℤ) i : ℝ) + 1
      simpa only [Pi.zero_apply, Int.cast_zero, zero_add, y] using
        And.intro (sub_nonneg.mpr h.1) (sub_le_iff_le_add'.mpr h.2)
    · unfold torusPoint
      rw [expShift_mk, ← mul_assoc, ← expDiagonal_add]
      congr 2
      apply congrArg expDiagonal
      funext i
      simp [y]
  · rintro ⟨_, ⟨⟨y, k⟩, ⟨hy, _⟩, rfl⟩, rfl⟩
    let x : I → ℝ := fun i => m i + y i
    refine ⟨(x, k), ⟨?_, Set.mem_univ _⟩, ?_⟩
    · intro i hi
      have h : 0 ≤ y i ∧ y i ≤ 1 := by simpa using hy i hi
      change (m i : ℝ) ≤ x i ∧ x i ≤ (m i : ℝ) + 1
      exact ⟨le_add_of_nonneg_right h.1, by dsimp [x]; linarith [h.2]⟩
    · unfold torusPoint
      rw [expShift_mk, ← mul_assoc, ← expDiagonal_add]
      rfl

/-- The mass of a logarithmic Iwasawa box grows at most exponentially in the sum of
the absolute values of its integer coordinates. -/
theorem exists_measure_torusBox_le (D : ComplexQuotientMeasureData r) :
    ∃ A B : ℝ≥0, 1 ≤ B ∧
      ∀ m : I → ℤ, D.measure (torusBox m) ≤
        (A : ℝ≥0∞) * (B : ℝ≥0∞) ^ (∑ i, (m i).natAbs) := by
  classical
  let step (i : I) (b : Bool) : I → ℝ := Pi.single i (if b then 1 else -1)
  have hfactor (i : I) (b : Bool) := exists_measure_image_expShift D (step i b)
  choose c _ hc using hfactor
  let B : ℝ≥0 := max 1 (∑ i, (c i true + c i false))
  have hB : 1 ≤ B := le_max_left _ _
  have hcB (i : I) (b : Bool) : c i b ≤ B := by
    apply le_trans _ (le_max_right _ _)
    have hi : c i true + c i false ≤ ∑ j, (c j true + c j false) :=
      Finset.single_le_sum (f := fun j : I => c j true + c j false)
        (fun _ _ => by positivity) (Finset.mem_univ i)
    cases b
    · exact (le_add_of_nonneg_left (by positivity)).trans hi
    · exact (le_add_of_nonneg_right (by positivity)).trans hi
  let bound (n : ℕ) (x : I → ℝ) : Prop :=
    ∀ S : Set Q, MeasurableSet S →
      D.measure (expShift x '' S) ≤ (B : ℝ≥0∞) ^ n * D.measure S
  have hstep (i : I) (b : Bool) : bound 1 (step i b) := by
    intro S hS
    rw [hc i b S hS, pow_one]
    gcongr
    exact hcB i b
  have hzero : bound 0 0 := by
    intro S _
    simp [expShift_zero]
  have hadd {a b : ℕ} {x y : I → ℝ} (hx : bound a x) (hy : bound b y) :
      bound (a + b) (x + y) := by
    intro S hS
    have heq : expShift (x + y) '' S = expShift x '' (expShift y '' S) := by
      rw [← Set.image_comp]
      congr 1
      funext q
      exact expShift_add x y q
    have hSy : MeasurableSet (expShift y '' S) := by
      have hpre : expShift y '' S = (expShift y).symm ⁻¹' S :=
        (expShift y).toEquiv.image_eq_preimage_symm S
      rw [hpre]
      exact (expShift y).symm.continuous.measurable hS
    rw [heq, pow_add, mul_assoc]
    apply (hx _ hSy).trans
    gcongr
    exact hy _ hS
  have hnat (i : I) (b : Bool) (n : ℕ) : bound n (n • step i b) := by
    induction n with
    | zero => simpa only [zero_nsmul] using hzero
    | succ n ih =>
      simpa only [Nat.succ_eq_add_one, succ_nsmul] using hadd ih (hstep i b)
  have hint (i : I) (m : ℤ) : bound m.natAbs (Pi.single i (m : ℝ)) := by
    cases m with
    | ofNat n =>
      change bound n (Pi.single i (n : ℝ))
      have hv : Pi.single i (n : ℝ) = n • step i true := by
        funext j
        by_cases h : j = i
        · subst j
          simp [step, nsmul_eq_mul]
        · simp [step, Pi.single_eq_of_ne h]
      rw [hv]
      exact hnat i true n
    | negSucc n =>
      change bound (n + 1) (Pi.single i ((Int.negSucc n : ℤ) : ℝ))
      have hv : Pi.single i ((Int.negSucc n : ℤ) : ℝ) = (n + 1) • step i false := by
        funext j
        by_cases h : j = i
        · subst j
          simp [step, nsmul_eq_mul, Int.cast_negSucc]
        · simp [step, Pi.single_eq_of_ne h]
      rw [hv]
      exact hnat i false (n + 1)
  have hvec (m : I → ℤ) (s : Finset I) :
      bound (∑ i ∈ s, (m i).natAbs) (∑ i ∈ s, Pi.single i (m i : ℝ)) := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using hzero
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact hadd (hint i (m i)) ih
  have hsum (m : I → ℤ) : (∑ i : I, Pi.single i (m i : ℝ)) = fun i => (m i : ℝ) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  let := leftQuotient_t2Space N GeneralLinear.UpperUnipotent.isClosed
  let := D.unipotentHaar_rightInvariant
  let := D.compatible.regular
  let A := (D.measure (torusBox (0 : I → ℤ))).toNNReal
  have hA : (A : ℝ≥0∞) = D.measure (torusBox (0 : I → ℤ)) :=
    ENNReal.coe_toNNReal (isCompact_torusBox (0 : I → ℤ)).measure_lt_top.ne
  refine ⟨A, B, hB, fun m => ?_⟩
  rw [torusBox_eq_shift, hA, mul_comm]
  have h := hvec m Finset.univ
  rw [hsum] at h
  exact h _ (isCompact_torusBox _).measurableSet

end Langlands.Global.RankinSelbergGlobal.ComplexLocalConvergence

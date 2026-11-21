import Langlands.Representation.Archimedean.RealCartanAngularHaar
import Langlands.Representation.Archimedean.RealCartanLowerCoordinates
import Langlands.Representation.Archimedean.RealLeviCompactChartSupport

/-! # Product angular coordinates for the compact real Levi blocks -/

noncomputable section

open Matrix MeasureTheory Set Metric
open scoped Matrix.Norms.Operator ENNReal

namespace Langlands.Archimedean.RealCartanAngularFrame

open RealCartanAngularHaar RealSmallOrthogonalHaar RealCartanPeakTest RealCartanLowerCoordinates
  RealLeviChart RealLeviCompactChart RealPrincipalSeriesDuality GramFormula

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

local notation "K" n:max => Matrix.unitaryGroup (Fin n) ℝ
local notation "L" n:max => (LowerIndex n → ℝ)

attribute [local instance] measurableSpaceK RealLeviBlockHaar.secondCountableTopology_GL
  RealLeviBlockHaar.secondCountableTopology_O
local instance borelSpaceK (n : ℕ) : BorelSpace (unitaryCompact ℝ n) := ⟨rfl⟩

section Coordinates

variable {c : ℕ} (sz : Fin c → ℕ)
local notation "ZSpace" => (WithinIndex sz → ℝ)

/-- The ambient within-block lower position corresponding to a local lower entry. -/
def withinAt (i : Fin c) (p : LowerIndex (sz i)) : WithinIndex sz :=
  ⟨⟨(pos sz i p.1.1, pos sz i p.1.2), by
      change (pos sz i p.1.2).val < (pos sz i p.1.1).val
      rw [val_pos, val_pos]
      exact Nat.add_lt_add_left p.2 _⟩,
    by simp [cls_pos]⟩

/-- Group the ambient within-block position set by its Levi block. -/
def withinEquivSigma : (Σ i : Fin c, LowerIndex (sz i)) ≃ WithinIndex sz :=
  Equiv.ofBijective (fun p => withinAt sz p.1 p.2) (by
    constructor
    · rintro ⟨i, p⟩ ⟨j, q⟩ h
      have he := congrArg (fun r : WithinIndex sz => cls sz r.1.1.1) h
      change cls sz (pos sz i p.1.1) = cls sz (pos sz j q.1.1) at he
      simp only [cls_pos] at he
      subst j
      congr 1
      apply Subtype.ext
      have hp (a b : Fin (sz i)) (hpos : pos sz i a = pos sz i b) : a = b := by
        apply Fin.ext
        have hv := congrArg Fin.val hpos
        rw [val_pos, val_pos] at hv
        omega
      exact Prod.ext (hp _ _ (congrArg (fun r : WithinIndex sz => r.1.1.1) h))
        (hp _ _ (congrArg (fun r : WithinIndex sz => r.1.1.2) h))
    · intro p
      obtain ⟨a, ha⟩ := pos_cls sz p.1.1.1
      obtain ⟨b, hb⟩ := pos_cls sz p.1.1.2
      let i := cls sz p.1.1.1
      obtain ⟨b', hb'⟩ : ∃ b' : Fin (sz i), pos sz i b' = p.1.1.2 := by
        dsimp [i]
        rw [← cls_eq_of_withinIndex sz p]
        exact ⟨b, hb⟩
      have hab : b' < a := by
        have hp := p.1.2
        rw [← ha, ← hb'] at hp
        change (pos sz i b').val < (pos sz i a).val at hp
        rw [val_pos, val_pos] at hp
        exact Nat.lt_of_add_lt_add_left hp
      exact ⟨⟨i, ⟨(a, b'), hab⟩⟩, Subtype.ext (Subtype.ext (Prod.ext ha hb'))⟩)

@[simp]
theorem withinEquivSigma_apply (i : Fin c) (p : LowerIndex (sz i)) :
    withinEquivSigma sz ⟨i, p⟩ = withinAt sz i p := rfl

private def splitAngles : ZSpace ≃ᵐ ((i : Fin c) → L (sz i)) :=
  (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (withinEquivSigma sz).symm).trans
    (MeasurableEquiv.piCurry fun _ _ => ℝ)

private theorem splitAngles_apply (Z : ZSpace) (i : Fin c) (p : LowerIndex (sz i)) :
    splitAngles sz Z i p = Z (withinAt sz i p) := by
  rw [splitAngles, MeasurableEquiv.trans_apply, MeasurableEquiv.coe_piCurry]
  change MeasurableEquiv.piCongrLeft (fun _ => ℝ) (withinEquivSigma sz).symm Z ⟨i, p⟩ = _
  rw [← show (withinEquivSigma sz).symm (withinAt sz i p) = ⟨i, p⟩ by simp [← withinEquivSigma_apply]]
  exact MeasurableEquiv.piCongrLeft_apply_apply (withinEquivSigma sz).symm
    (β := fun _ => ℝ) Z _

private theorem splitAngles_symm_apply (z : (i : Fin c) → L (sz i)) (i : Fin c)
    (p : LowerIndex (sz i)) : (splitAngles sz).symm z (withinAt sz i p) = z i p := by
  exact (splitAngles_apply sz ((splitAngles sz).symm z) i p).symm.trans
    (congrFun (congrFun ((splitAngles sz).apply_symm_apply z) i) p)

private abbrev angleMeasure (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  volume.restrict (closedBall 0 Real.pi)

private theorem angleMeasure_eq_pi (ι : Type*) [Fintype ι] :
    angleMeasure ι = Measure.pi fun _ : ι => volume.restrict angleInterval := by
  rw [angleMeasure, closedBall_pi 0 Real.pi_pos.le]
  simp only [Pi.zero_apply, Real.closedBall_eq_Icc, zero_sub, zero_add, volume_pi, Measure.restrict_pi_pi]

private theorem measurePreserving_splitAngles :
    MeasurePreserving (splitAngles sz) (angleMeasure (WithinIndex sz))
      (Measure.pi fun i : Fin c => angleMeasure (LowerIndex (sz i))) := by
  let e := splitAngles sz
  apply MeasurePreserving.symm e.symm
  refine ⟨e.symm.measurable, ?_⟩
  rw [angleMeasure_eq_pi (WithinIndex sz)]
  refine (Measure.pi_eq fun s _ => ?_).symm
  rw [e.symm.map_apply]
  have he : e.symm ⁻¹' (univ.pi s) = univ.pi (fun i => univ.pi (fun p => s (withinAt sz i p))) := by
    ext z
    simp only [mem_preimage, mem_univ_pi]
    constructor
    · intro h i p
      simpa only [e, splitAngles_symm_apply] using h (withinAt sz i p)
    · intro h q
      obtain ⟨⟨i, p⟩, rfl⟩ := (withinEquivSigma sz).surjective q
      simpa only [withinEquivSigma_apply, e, splitAngles_symm_apply] using h i p
  rw [he, Measure.pi_pi]
  simp_rw [angleMeasure_eq_pi, Measure.pi_pi]
  rw [← Fintype.prod_sigma']
  exact Fintype.prod_equiv (withinEquivSigma sz) _ _ (fun ⟨_, _⟩ => rfl)

end Coordinates

section Blocks

private def lowerTwo : LowerIndex 2 := ⟨(1, 0), by decide⟩

private instance lowerOneIsEmpty : IsEmpty (LowerIndex 1) :=
  ⟨fun p => by have := p.2; omega⟩

private instance lowerTwoUnique : Unique (LowerIndex 2) where
  default := lowerTwo
  uniq p := by
    have hp := p.2
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext
    · change p.1.1.val = 1
      omega
    · change p.1.2.val = 0
      omega

/-- The local lower entry of a plane in its block coordinates. -/
def pairLower {n : ℕ} (h : n = 2) : LowerIndex n := h.symm ▸ lowerTwo

/-- The angular parameterization inside a single line or plane. -/
def angularBlock (n : ℕ) (z : L n) : K n :=
  if h : n = 2 then (h.symm ▸ rotation (z (pairLower h))) else 1

@[simp]
theorem angularBlock_one (z : L 1) : angularBlock 1 z = 1 := by simp [angularBlock]

@[simp]
theorem angularBlock_two (z : L 2) : angularBlock 2 z = rotation (z lowerTwo) := by
  simp [angularBlock, pairLower]

theorem continuous_angularBlock (n : ℕ) : Continuous (angularBlock n) := by
  by_cases h : n = 2
  · subst n
    exact (continuous_rotation.comp (continuous_apply lowerTwo)).congr (fun z => (angularBlock_two z).symm)
  · exact (continuous_const : Continuous fun _ : L n => (1 : K n)).congr
      (fun z => by simp [angularBlock, h])

@[simp]
theorem angularBlock_zero (n : ℕ) : angularBlock n 0 = 1 := by
  by_cases h : n = 2
  · subst n
    simp only [angularBlock_two, Pi.zero_apply]
    exact (rotation_eq_one_iff (mem_Icc.mpr ⟨by linarith [Real.pi_pos], Real.pi_pos.le⟩)).2 rfl
  · simp [angularBlock, h]

theorem angularBlock_eq_one_iff (n : ℕ) (hn : n = 1 ∨ n = 2) (z : L n)
    (hz : z ∈ closedBall 0 Real.pi) : angularBlock n z = 1 ↔ z = 0 := by
  rcases hn with h | h
  · subst n
    simp only [angularBlock_one, true_iff]
    exact Subsingleton.elim _ _
  · subst n
    have hθ : z lowerTwo ∈ angleInterval := by
      rw [closedBall_pi _ Real.pi_pos.le, mem_univ_pi] at hz
      simpa only [Pi.zero_apply, Real.closedBall_eq_Icc, zero_sub, zero_add] using hz lowerTwo
    rw [angularBlock_two, rotation_eq_one_iff hθ]
    constructor
    · intro h
      funext j
      rw [Subsingleton.elim j lowerTwo]
      exact h
    · rintro rfl
      rfl

/-- The angular Haar coefficients for an orthogonal line and plane. -/
def angularCoefficient (n : ℕ) : ℝ := if n = 2 then (4 * Real.pi)⁻¹ else 2⁻¹

theorem angularCoefficient_pos (n : ℕ) : 0 < angularCoefficient n := by
  unfold angularCoefficient
  split <;> positivity

private theorem angularBlock_map (n : ℕ) (hn : n = 1 ∨ n = 2) :
    (compactHaar n).restrict (positiveComponent n) = ENNReal.ofReal (angularCoefficient n) •
      (angleMeasure (LowerIndex n)).map (angularBlock n) := by
  rcases hn with h | h
  · subst n
    rw [restrict_positive_one]
    simp only [angularCoefficient, Nat.reduceEqDiff, ite_false, angleMeasure]
    rw [show closedBall (0 : L 1) Real.pi = univ by
      ext z
      rw [Subsingleton.elim z 0]
      exact iff_of_true (mem_closedBall_self Real.pi_pos.le) trivial,
      Measure.restrict_univ, Measure.volume_pi_eq_dirac (0 : L 1),
      Measure.map_dirac (0 : L 1), angularBlock_one]
  · subst n
    rw [restrict_positive_two]
    simp only [angularCoefficient, ite_true]
    congr 1
    let e := MeasurableEquiv.funUnique (LowerIndex 2) ℝ
    have he (z : L 2) : e z = z lowerTwo := rfl
    have hs : e ⁻¹' angleInterval = closedBall (0 : L 2) Real.pi := by
      ext z
      rw [closedBall_pi _ Real.pi_pos.le, mem_univ_pi, mem_preimage, he]
      exact ⟨fun hz j => by
        rw [Subsingleton.elim j lowerTwo]
        simpa only [Pi.zero_apply, Real.closedBall_eq_Icc, zero_sub, zero_add] using hz,
        fun hz => by
          simpa only [Pi.zero_apply, Real.closedBall_eq_Icc, zero_sub, zero_add] using hz lowerTwo⟩
    have hm : (angleMeasure (LowerIndex 2)).map e = volume.restrict angleInterval := by
      rw [angleMeasure, ← hs, ← e.restrict_map, (volume_preserving_funUnique _ _).map_eq]
    rw [← hm, Measure.map_map continuous_rotation.measurable e.measurable]
    rfl

end Blocks

section Frames

variable {c : ℕ} (sz : Fin c → ℕ)
local notation "ZSpace" => (WithinIndex sz → ℝ)
local notation "H" => LeviFrame sz

private theorem continuous_compactEquiv_symm (n : ℕ) : Continuous (compactEquiv n).symm :=
  (continuous_unitary_toUnits (F := ℝ) (N := n)).subtype_mk _

/-- A compact Levi frame in the identity component, given its within-block angles. -/
def angularFrame (Z : ZSpace) : H :=
  fun i => (compactEquiv (sz i)).symm (angularBlock (sz i) (fun p => Z (withinAt sz i p)))

theorem continuous_angularFrame : Continuous (angularFrame sz) := by
  exact continuous_pi fun i => (continuous_compactEquiv_symm _).comp
    ((continuous_angularBlock _).comp (continuous_pi fun p => continuous_apply (withinAt sz i p)))

@[simp]
theorem angularFrame_zero : angularFrame sz 0 = 1 := by
  funext i
  change (compactEquiv (sz i)).symm (angularBlock (sz i) 0) = 1
  rw [angularBlock_zero, map_one]

theorem angularFrame_eq_one_iff (hsize : ∀ i, sz i = 1 ∨ sz i = 2)
    (Z : ZSpace) (hZ : Z ∈ closedBall 0 Real.pi) : angularFrame sz Z = 1 ↔ Z = 0 := by
  constructor
  · intro h
    funext q
    obtain ⟨⟨i, p⟩, rfl⟩ := (withinEquivSigma sz).surjective q
    have hz : (fun p => Z (withinAt sz i p)) ∈ closedBall (0 : L (sz i)) Real.pi := by
      rw [closedBall_pi _ Real.pi_pos.le, mem_univ_pi] at hZ ⊢
      exact fun p => hZ (withinAt sz i p)
    have hi := congrFun h i
    change (compactEquiv (sz i)).symm (angularBlock (sz i) (fun p => Z (withinAt sz i p))) = 1 at hi
    rw [← map_one (compactEquiv (sz i)).symm, EmbeddingLike.apply_eq_iff_eq] at hi
    exact congrFun ((angularBlock_eq_one_iff _ (hsize i) _ hz).mp hi) p
  · rintro rfl
    exact angularFrame_zero sz

/-- The determinant-one locus in every compact factor. -/
def positiveFrame : Set H := univ.pi fun i => (compactEquiv (sz i)) ⁻¹' positiveComponent (sz i)

theorem isClopen_positiveFrame : IsClopen (positiveFrame sz) := by
  exact ⟨isClosed_set_pi fun i _ => (isClopen_positiveComponent _).1.preimage (continuous_compactEquiv _),
    isOpen_set_pi finite_univ fun i _ => (isClopen_positiveComponent _).2.preimage (continuous_compactEquiv _)⟩

@[simp]
theorem one_mem_positiveFrame : (1 : H) ∈ positiveFrame sz := by
  simp [positiveFrame]

private theorem haarK_restrict_block (n : ℕ) (hn : n = 1 ∨ n = 2) :
    (haarK n).restrict ((compactEquiv n) ⁻¹' positiveComponent n) =
      ENNReal.ofReal (angularCoefficient n) • (angleMeasure (LowerIndex n)).map
        (fun z => (compactEquiv n).symm (angularBlock n z)) := by
  let e : unitaryCompact ℝ n ≃ᵐ K n :=
    ⟨(compactEquiv n).toEquiv, (continuous_compactEquiv n).measurable,
      (continuous_compactEquiv_symm n).measurable⟩
  change (haarK n).restrict (e ⁻¹' positiveComponent n) = _
  rw [← MeasurableEquiv.map_symm_map (μ := (haarK n).restrict (e ⁻¹' positiveComponent n)) e,
    ← e.restrict_map]
  change ((compactHaar n).restrict (positiveComponent n)).map e.symm = _
  rw [angularBlock_map n hn, Measure.map_smul _ e.symm.measurable.aemeasurable,
    Measure.map_map e.symm.measurable (continuous_angularBlock n).measurable]
  rfl

private theorem pi_smul_measure {ι : Type*} [Fintype ι] {A : ι → Type*}
    [∀ i, MeasurableSpace (A i)] (p : ι → ℝ≥0∞) (μ : ∀ i, Measure (A i)) [∀ i, SigmaFinite (μ i)]
    [∀ i, SigmaFinite (p i • μ i)] :
    Measure.pi (fun i => p i • μ i) = (∏ i, p i) • Measure.pi μ := by
  refine Measure.pi_eq (μ := fun i => p i • μ i) fun s _ => ?_
  simp only [Measure.smul_apply, smul_eq_mul, Measure.pi_pi, Finset.prod_mul_distrib]

/-- The product Haar coefficient of the within-block angular coordinates. -/
def frameCoefficient : ℝ := ∏ i, angularCoefficient (sz i)

theorem frameCoefficient_pos : 0 < frameCoefficient sz :=
  Finset.prod_pos fun _ _ => angularCoefficient_pos _

/-- Haar measure on the determinant-one Levi frames in the within-block angles. -/
def RealCartanAngularFrameStatement : Prop :=
  ∀ (c : ℕ) (sz : Fin c → ℕ), (∀ i, sz i = 1 ∨ sz i = 2) →
    (frameMeasure sz).restrict (positiveFrame sz) = ENNReal.ofReal (frameCoefficient sz) •
      (volume.restrict (closedBall 0 Real.pi)).map (angularFrame sz)

set_option maxHeartbeats 500000 in
theorem realCartanAngularFrame : RealCartanAngularFrameStatement := by
  intro c sz hsize
  rw [positiveFrame, Measure.restrict_pi_pi]
  simp_rw [haarK_restrict_block _ (hsize _)]
  let f (i : Fin c) (z : L (sz i)) := (compactEquiv (sz i)).symm (angularBlock (sz i) z)
  have hm (i : Fin c) : Measurable (f i) :=
    ((continuous_compactEquiv_symm _).comp (continuous_angularBlock _)).measurable
  have (i : Fin c) : IsFiniteMeasure (angleMeasure (LowerIndex (sz i))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact IsCompact.measure_lt_top (isCompact_closedBall _ _)⟩
  have (i : Fin c) : IsFiniteMeasure (ENNReal.ofReal (angularCoefficient (sz i)) •
      (angleMeasure (LowerIndex (sz i))).map (f i)) :=
    ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)⟩
  rw [pi_smul_measure, ← Measure.pi_map_pi (fun i => (hm i).aemeasurable)]
  have hmap : Measurable (fun (z : (i : Fin c) → L (sz i)) i => f i (z i)) :=
    Measurable.of_eval fun i => (hm i).comp (measurable_pi_apply i)
  rw [← (measurePreserving_splitAngles sz).map_eq, Measure.map_map hmap (splitAngles sz).measurable]
  congr 1
  · rw [frameCoefficient, ENNReal.ofReal_prod_of_nonneg fun i _ => (angularCoefficient_pos _).le]
  · congr 1
    funext Z i
    change f i (splitAngles sz Z i) = f i (fun p => Z (withinAt sz i p))
    exact congrArg (f i) (funext (splitAngles_apply sz Z i))

end Frames

end Langlands.Archimedean.RealCartanAngularFrame

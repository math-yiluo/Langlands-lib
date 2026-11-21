import Langlands.Analysis.L2SlabRecurrence

/-! # Independent one-sided translation recurrences in `L²`

The finite-direction extension of the slab estimate for Bernstein–Lapid §7.5.
Only invariance of each height under the other shifts is needed.
-/

noncomputable section
set_option autoImplicit false

namespace Langlands.Analysis

open MeasureTheory Set
open scoped ENNReal NNReal

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

namespace L2RenormalizingShift

/-- Restriction of a renormalizing shift to the measure on an invariant measurable
set. The underlying transformations on points are unchanged. -/
def restrict (H : L2RenormalizingShift μ) (A : Set X) (hA : MeasurableSet A)
    (hinv : H.shift ⁻¹' A = A) : L2RenormalizingShift (μ.restrict A) where
  shift := H.shift
  measurable_shift := H.measurable_shift
  height := H.height
  measurable_height := H.measurable_height
  height_shift := H.height_shift
  factor := H.factor
  factor_pos := H.factor_pos
  map_shift := by
    calc
      Measure.map H.shift (μ.restrict A) = (Measure.map H.shift μ).restrict A := by
        rw [Measure.restrict_map H.measurable_shift hA, hinv]
      _ = H.factor ^ (2 : ℕ) • μ.restrict A := by
        rw [H.map_shift, Measure.restrict_smul]

/-- Weighted sum of the norms of the lower coefficients. -/
def lowerMass (H : L2RenormalizingShift μ) {m : ℕ} (p : Fin m → ℂ) : ℝ :=
  ∑ k, ‖p k‖ * (H.factor : ℝ) ^ (k : ℕ)

/-- A simultaneous bound for the two coefficients of the one-direction estimate. -/
def slabMajorant (H : L2RenormalizingShift μ) {m : ℕ} (p : Fin m → ℂ) : ℝ :=
  ((H.factor : ℝ) ^ m + 1) / ((H.factor : ℝ) ^ m - H.lowerMass p)

/-- A convenient sufficient hypothesis for the lower-coefficient estimate. -/
theorem lowerMass_lt_of_sum_lt (H : L2RenormalizingShift μ) {m : ℕ} (p : Fin m → ℂ)
    (hc : 1 ≤ H.factor) (hp : ∑ k, ‖p k‖ < (H.factor : ℝ)) :
    H.lowerMass p < (H.factor : ℝ) ^ m := by
  cases m with
  | zero => simp [lowerMass]
  | succ m =>
    have hc' : 1 ≤ (H.factor : ℝ) := by exact_mod_cast hc
    have hcm : 0 < (H.factor : ℝ) ^ m := pow_pos (by exact_mod_cast H.factor_pos) _
    calc
      H.lowerMass p ≤ (∑ k, ‖p k‖) * (H.factor : ℝ) ^ m := by
        rw [lowerMass, Finset.sum_mul]
        exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hc' (Nat.le_of_lt_succ k.isLt)) (norm_nonneg _)
      _ < (H.factor : ℝ) * (H.factor : ℝ) ^ m := mul_lt_mul_of_pos_right hp hcm
      _ = (H.factor : ℝ) ^ (m + 1) := (pow_succ' _ _).symm

end L2RenormalizingShift

namespace L2IndependentSlabs

variable {ι : Type*} {t : Finset ι}

/-- The intersection of the positive half-spaces of the selected heights. -/
def positiveRegion (H : (↑t : Type _) → L2RenormalizingShift μ) : Set X :=
  ⋂ i : (↑t : Type _), (H i).positive

/-- The intersection of the initial slabs, with the degree of each equation as
its upper endpoint. -/
def boundaryBox (H : (↑t : Type _) → L2RenormalizingShift μ) (m : ι → ℕ) : Set X :=
  ⋂ i : (↑t : Type _), (H i).slab 0 (m i)

/-- Each shift leaves all the other height coordinates unchanged. -/
def Independent (H : (↑t : Type _) → L2RenormalizingShift μ) : Prop :=
  ∀ i j : (↑t : Type _), i ≠ j → ∀ x, (H j).height ((H i).shift x) = (H j).height x

theorem measurable_positiveRegion (H : (↑t : Type _) → L2RenormalizingShift μ) :
    MeasurableSet (positiveRegion H) :=
  MeasurableSet.iInter fun i => (H i).measurable_height measurableSet_Ioi

theorem measurable_boundaryBox (H : (↑t : Type _) → L2RenormalizingShift μ) (m : ι → ℕ) :
    MeasurableSet (boundaryBox H m) :=
  MeasurableSet.iInter fun i => (H i).measurable_slab 0 (m i)

omit [MeasurableSpace X] in
private theorem iInter_insert [DecidableEq ι] (i : ι) (F : (↑(insert i t) : Type _) → Set X) :
    (⋂ j, F j) = F ⟨i, Finset.mem_insert_self i t⟩ ∩
      ⋂ j : (↑t : Type _), F ⟨j, Finset.mem_insert_of_mem j.2⟩ := by
  ext x
  simp only [mem_iInter, mem_inter_iff]
  refine ⟨fun hx => ⟨hx _, fun _ => hx _⟩, ?_⟩
  intro hx j
  rcases Finset.mem_insert.mp j.2 with he | hj
  · have hej : j = ⟨i, Finset.mem_insert_self i t⟩ := Subtype.ext he
    rw [hej]
    exact hx.1
  · exact hx.2 ⟨j, hj⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : X → E}

omit [NormedSpace ℂ E] in
private theorem norm_restrict_mono {S T : Set X} {g : X → E} (hST : S ⊆ T)
    (hg : MemLp g 2 (μ.restrict T)) :
    lpNorm g 2 (μ.restrict S) ≤ lpNorm g 2 (μ.restrict T) :=
  ENNReal.toReal_mono hg.eLpNorm_ne_top (eLpNorm_mono_measure _ (μ.restrict_mono_set hST))

private theorem norm_le_majorant (H : L2RenormalizingShift μ) {m : ℕ} (p : Fin m → ℂ)
    (hsmall : H.lowerMass p < (H.factor : ℝ) ^ m)
    {a b d K : ℝ} (hb : 0 ≤ b) (hd : 0 ≤ d) (hK : H.slabMajorant p ≤ K)
    (ha : a ≤ ((H.factor : ℝ) ^ m * b + d) / ((H.factor : ℝ) ^ m - H.lowerMass p)) :
    a ≤ K * (b + d) := by
  refine ha.trans ((?_ : _ ≤ H.slabMajorant p * (b + d)).trans
    (mul_le_mul_of_nonneg_right hK (add_nonneg hb hd)))
  rw [L2RenormalizingShift.slabMajorant, div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ (sub_nonneg.mpr hsmall.le)
  have hn : 0 ≤ (H.factor : ℝ) ^ m * d := mul_nonneg (pow_nonneg H.factor.2 _) hd
  nlinarith only [hb, hn]

/-- Square-integrability and a common norm bound on the positive region, from
the boundary box and all the difference residuals. The number `K ≥ 1` bounds
the one-direction majorants and `R ≥ 0` bounds all the input norms. -/
theorem memLp_and_lpNorm_le (H : (↑t : Type _) → L2RenormalizingShift μ)
    (hH : Independent H) (m : ι → ℕ) (p : ∀ i, Fin (m i) → ℂ) (hf : StronglyMeasurable f)
    {K R : ℝ} (hK : 1 ≤ K) (hR : 0 ≤ R)
    (hsmall : ∀ i : (↑t : Type _), (H i).lowerMass (p i) < ((H i).factor : ℝ) ^ (m i))
    (hmajor : ∀ i : (↑t : Type _), (H i).slabMajorant (p i) ≤ K)
    (hbox : MemLp f 2 (μ.restrict (boundaryBox H m)))
    (hbox_le : lpNorm f 2 (μ.restrict (boundaryBox H m)) ≤ R)
    (hres : ∀ i : (↑t : Type _), MemLp ((H i).residual (p i) f) 2 (μ.restrict (positiveRegion H)))
    (hres_le : ∀ i : (↑t : Type _), lpNorm ((H i).residual (p i) f) 2 (μ.restrict (positiveRegion H)) ≤ R) :
    MemLp f 2 (μ.restrict (positiveRegion H)) ∧
      lpNorm f 2 (μ.restrict (positiveRegion H)) ≤ (2 * K) ^ t.card * R := by
  classical
  induction t using Finset.induction_on generalizing μ with
  | empty =>
    simpa [positiveRegion, boundaryBox] using And.intro hbox hbox_le
  | @insert i t hit ih =>
    let i₀ : (↑(insert i t) : Type _) := ⟨i, Finset.mem_insert_self i t⟩
    let prev (j : (↑t : Type _)) : (↑(insert i t) : Type _) := ⟨j, Finset.mem_insert_of_mem j.2⟩
    have hneq (j : (↑t : Type _)) : prev j ≠ i₀ := by
      intro hij
      have hj : (j : ι) = i := congrArg Subtype.val hij
      exact hit (hj ▸ j.2)
    let B := (H i₀).slab 0 (m i)
    let P := positiveRegion (fun j => H (prev j))
    have hBm : MeasurableSet B := (H i₀).measurable_slab _ _
    have hPm : MeasurableSet P := measurable_positiveRegion _
    have hB (j : (↑t : Type _)) : (H (prev j)).shift ⁻¹' B = B := by
      ext x
      simp only [B, L2RenormalizingShift.slab, mem_preimage, hH _ _ (hneq j) x]
    have hP : (H i₀).shift ⁻¹' P = P := by
      ext x
      have he (j : (↑t : Type _)) := hH i₀ (prev j) (hneq j).symm x
      simp only [P, positiveRegion, L2RenormalizingShift.positive, mem_preimage, mem_iInter, he]
    let H' (j : (↑t : Type _)) := (H (prev j)).restrict B hBm (hB j)
    let H₀ := (H i₀).restrict P hPm hP
    have hH' : Independent H' := fun j l hjl x =>
      hH (prev j) (prev l) (fun h => hjl (Subtype.ext
        (congrArg (fun j : (↑(insert i t) : Type _) => (j : ι)) h))) x
    have hPbox : boundaryBox H m = B ∩ boundaryBox H' m := by
      rw [boundaryBox, iInter_insert]
      rfl
    have hPpos : positiveRegion H = (H i₀).positive ∩ P := by
      rw [positiveRegion, iInter_insert]
      rfl
    have hμbox : (μ.restrict B).restrict (boundaryBox H' m) = μ.restrict (boundaryBox H m) := by
      rw [Measure.restrict_restrict (measurable_boundaryBox H' m), inter_comm, ← hPbox]
    have hμpos : (μ.restrict B).restrict (positiveRegion H') = μ.restrict (B ∩ P) := by
      change (μ.restrict B).restrict P = _
      rw [Measure.restrict_restrict hPm, inter_comm]
    have hsub : B ∩ P ⊆ positiveRegion H := by
      rw [hPpos]
      exact inter_subset_inter_left _ ((H i₀).slab_subset_positive 0 _ le_rfl)
    have hres' (j : (↑t : Type _)) :
        MemLp ((H' j).residual (p j) f) 2 ((μ.restrict B).restrict (positiveRegion H')) := by
      rw [hμpos]
      exact (hres (prev j)).mono_measure (μ.restrict_mono_set hsub)
    have hres_le' (j : (↑t : Type _)) :
        lpNorm ((H' j).residual (p j) f) 2 ((μ.restrict B).restrict (positiveRegion H')) ≤ R := by
      rw [hμpos]
      exact (norm_restrict_mono hsub (hres (prev j))).trans (hres_le (prev j))
    have hbox' : MemLp f 2 ((μ.restrict B).restrict (boundaryBox H' m)) := hμbox ▸ hbox
    have hbox_le' : lpNorm f 2 ((μ.restrict B).restrict (boundaryBox H' m)) ≤ R := hμbox ▸ hbox_le
    obtain ⟨hmid, hmid_le⟩ := ih H' hH' (fun j => hsmall (prev j)) (fun j => hmajor (prev j))
      hbox' hbox_le' hres' hres_le'
    have hμslab₀ : (μ.restrict P).restrict (H₀.slab 0 (m i)) =
        (μ.restrict B).restrict (positiveRegion H') := by
      change (μ.restrict P).restrict B = _
      rw [Measure.restrict_restrict hBm, hμpos]
    have hμpos₀ : (μ.restrict P).restrict H₀.positive = μ.restrict (positiveRegion H) := by
      change (μ.restrict P).restrict (H i₀).positive = _
      have hs : MeasurableSet (H i₀).positive := (H i₀).measurable_height measurableSet_Ioi
      rw [Measure.restrict_restrict hs, ← hPpos]
    have hbase₀ : MemLp f 2 ((μ.restrict P).restrict (H₀.slab 0 (m i))) := hμslab₀ ▸ hmid
    have hres₀ : MemLp (H₀.residual (p i) f) 2 ((μ.restrict P).restrict H₀.positive) := by
      rw [hμpos₀]
      exact hres i₀
    obtain ⟨hm, hnorm⟩ := H₀.memLp_positive_and_lpNorm_le (p i) hf (hsmall i₀) hbase₀ hres₀
    have hbound := norm_le_majorant H₀ (p i) (hsmall i₀) lpNorm_nonneg lpNorm_nonneg (hmajor i₀) hnorm
    rw [hμpos₀] at hm hbound
    rw [hμslab₀] at hbound
    refine ⟨hm, hbound.trans ?_⟩
    have hK0 : 0 ≤ K := zero_le_one.trans hK
    have hpow : 1 ≤ (2 * K) ^ t.card := one_le_pow₀ (by linarith : (1 : ℝ) ≤ 2 * K)
    have hR' : R ≤ (2 * K) ^ t.card * R := le_mul_of_one_le_left hR hpow
    calc
      _ ≤ K * ((2 * K) ^ t.card * R + R) := by
        apply mul_le_mul_of_nonneg_left (add_le_add hmid_le _) hK0
        exact hres_le i₀
      _ ≤ K * ((2 * K) ^ t.card * R + (2 * K) ^ t.card * R) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl hR') hK0
      _ = (2 * K) ^ (insert i t).card * R := by
        rw [Finset.card_insert_of_notMem hit, pow_succ]
        ring

end L2IndependentSlabs

open L2IndependentSlabs

universe u v w

/-- A finite family of renormalizing shifts with separate height coordinates admits
an `L²` estimate in terms of the boundary box and the sum of the residual norms.
Membership of the original function on the full positive region follows from those
inputs, rather than being assumed. -/
def L2IndependentSlabsStatement : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] {μ : Measure X} {ι : Type v} {t : Finset ι}
    (H : (↑t : Type v) → L2RenormalizingShift μ), Independent H →
    ∀ (m : ι → ℕ) (p : ∀ i, Fin (m i) → ℂ),
    (∀ i : (↑t : Type v), (H i).lowerMass (p i) < ((H i).factor : ℝ) ^ (m i)) →
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {E : Type w} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : X → E},
      StronglyMeasurable f → MemLp f 2 (μ.restrict (boundaryBox H m)) →
      (∀ i : (↑t : Type v), MemLp ((H i).residual (p i) f) 2 (μ.restrict (positiveRegion H))) →
      MemLp f 2 (μ.restrict (positiveRegion H)) ∧
        lpNorm f 2 (μ.restrict (positiveRegion H)) ≤ C *
          (lpNorm f 2 (μ.restrict (boundaryBox H m)) +
            ∑ i : (↑t : Type v), lpNorm ((H i).residual (p i) f) 2 (μ.restrict (positiveRegion H)))

/-- The multidirectional norm and membership estimate. -/
theorem l2IndependentSlabs : L2IndependentSlabsStatement.{u, v, w} := by
  intro X _ μ ι t H hind m p hsmall
  let K : ℝ := 1 + ∑ i : (↑t : Type v), |(H i).slabMajorant (p i)|
  have hK : 1 ≤ K := le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  have hmajor (i : (↑t : Type v)) : (H i).slabMajorant (p i) ≤ K := by
    refine (le_abs_self _).trans ?_
    have h : |(H i).slabMajorant (p i)| ≤ ∑ j : (↑t : Type v), |(H j).slabMajorant (p j)| :=
      Finset.single_le_sum (fun j _ => abs_nonneg ((H j).slabMajorant (p j))) (Finset.mem_univ i)
    exact h.trans (le_add_of_nonneg_left zero_le_one)
  refine ⟨(2 * K) ^ t.card, one_le_pow₀ (by linarith : (1 : ℝ) ≤ 2 * K), ?_⟩
  intro E _ _ f hf hbox hres
  let r (i : (↑t : Type v)) := lpNorm ((H i).residual (p i) f) 2 (μ.restrict (positiveRegion H))
  let b := lpNorm f 2 (μ.restrict (boundaryBox H m))
  have hr : 0 ≤ ∑ i, r i := Finset.sum_nonneg fun _ _ => lpNorm_nonneg
  refine memLp_and_lpNorm_le H hind m p hf hK (add_nonneg lpNorm_nonneg hr) hsmall hmajor hbox
    (le_add_of_nonneg_right hr) hres (fun i => ?_)
  have hi : r i ≤ ∑ j, r j := Finset.single_le_sum (fun j _ => show 0 ≤ r j from lpNorm_nonneg)
    (Finset.mem_univ i)
  exact hi.trans (le_add_of_nonneg_left (show 0 ≤ b from lpNorm_nonneg))

end Langlands.Analysis

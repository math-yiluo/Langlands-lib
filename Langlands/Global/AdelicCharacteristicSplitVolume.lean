import Langlands.Global.AdelicCharacteristicShellCoordinates
import Langlands.Global.AdelicRelativeCorootHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # The volume of a characteristic split shell -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Set
open scoped CategoryTheory.MonObj ENNReal NNReal Classical

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme GroupScheme.RealTorusSpace AdelicGroupPoints PositiveRealTorus ArthurRelative
  ArthurTruncation

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) (J : StandardIndex F G fam.i fam.ν)
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact (fam.p fam.bot) K)

local notation "T" => fam.T
local notation "D" => fam.coroots
local notation "Δ" => simpleRelativeRoots fam.i fam.ν
local notation "B" => relativePositiveSubgroup (fam.l J ≫ fam.p J) (fam.a J)
local notation "C" => fam.relativeSimpleRoots J
local notation "πJ" => levelProjection fam.connectedReductive fam.maximalSplit fam.ν D J.val
local notation "w" => weight fam.connectedReductive fam.maximalSplit fam.ν D Δ
local notation "H" => fun b : B => fam.minimalHeight hK (fam.relativeSplitPoint J b)

omit [NumberField F] in
private theorem relativeRoots_mem (α : C) : α.val ∈ Δ \ J.val := by
  have ha := Finset.mem_filter.mp α.property
  exact ⟨(mem_simpleFinset fam.connectedReductive fam.maximalSplit).mp ha.1, ha.2⟩

omit [NumberField F] in
private theorem weightCoordinate_eq_apply (x : V T) (α : C) :
    fam.weightCoordinate J x α = w α.val x := by
  have he : (simpleFinset fam.ν fam.connectedReductive fam.maximalSplit :
      Set (characterLattice T)) = Δ := Set.ext fun _ => mem_simpleFinset _ _
  unfold weightCoordinate
  rw [he]

omit [NumberField F] in
private theorem weight_projectedHeight (α : C) (x : V T) : w α.val (πJ x) = w α.val x := by
  have hα := fam.relativeRoots_mem J α
  have hspan : corootSubspace D J.val ≤ LinearMap.ker (w α.val) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨β, hβ, rfl⟩
    have hne : α.val ≠ β.val := fun he => hα.2 (he.symm ▸ hβ)
    change w α.val ((D).realCoroot β) = 0
    rw [weight_coroot fam.connectedReductive fam.maximalSplit D fam.generic subset_rfl hα.1 β
      (J.property hβ), ite_eq_right hne]
  have h := LinearMap.mem_ker.mp (hspan (sub_levelProjection_mem_span fam.connectedReductive
    fam.maximalSplit (ν := fam.ν) D J.val x))
  rwa [map_sub, sub_eq_zero, eq_comm] at h

omit [NumberField F] in
private theorem weight_projectedSimpleCoroot' (α β : C) :
    w α.val (fam.projectedSimpleCoroot J β).val = if α = β then 1 else 0 := by
  have ha := (fam.relativeRoots_mem J α).1
  have hb := (fam.relativeRoots_mem J β).1
  let r : relativeRoots fam.i := ⟨β.val, fam.mem_relativeRoots_of_mem_relativeSimpleRoots J β⟩
  change w α.val (πJ ((D).realCoroot r)) = _
  rw [fam.weight_projectedHeight J, weight_coroot fam.connectedReductive fam.maximalSplit D
    fam.generic subset_rfl ha r hb]
  simp only [Subtype.ext_iff, r]

omit [NumberField F] in
private theorem weight_nonneg_of_root_nonneg {x : V T} (hx : ∀ α ∈ Δ, 0 ≤ eval T α x)
    (α : C) : 0 ≤ w α.val x := by
  let := finite_indivisibleRoots fam.connectedReductive fam.maximalSplit
  let a : RelativeRoot.indivisibleRoots fam.i := ⟨α.val,
    simpleRelativeRoots_subset_indivisibleRoots fam.connectedReductive fam.maximalSplit fam.ν
      (fam.relativeRoots_mem J α).1⟩
  rw [← neg_nonpos, ← map_neg, show α.val = a.val from rfl, weight_coe]
  apply ArthurCombinatorics.weightCoordinate_nonpos
    (base fam.connectedReductive fam.maximalSplit fam.generic D)
    (standardIndex_subset_support fam.connectedReductive fam.maximalSplit D fam.generic Δ)
  intro β hβ
  have he := eval_sub_toCorootSpan fam.connectedReductive fam.maximalSplit D β.2.1 (-x)
  rw [map_sub, sub_eq_zero] at he
  calc
    _ = eval T β.1 (toCorootSpan fam.connectedReductive fam.maximalSplit D (-x)) := by
      rw [eval_eq_pair]; rfl
    _ = eval T β.1 (-x) := he.symm
    _ ≤ 0 := by
      rw [map_neg, neg_nonpos]
      exact hx β.1 ((mem_standardIndex fam.connectedReductive fam.maximalSplit fam.ν).mp hβ).2

omit [NumberField F] in
private theorem splitShell_weight_bounds {Tp S Y : V T}
    (hY : Y ∈ characteristicSplitShell fam.connectedReductive fam.maximalSplit D J Tp S)
    (α : C) : fam.weightCoordinate J Tp α ≤ w α.val Y ∧
      w α.val Y ≤ fam.weightCoordinate J (Tp + S) α := by
  have hroot (β : characterLattice T) (hb : β ∈ Δ) : 0 ≤ eval T β (Y - πJ Tp) := by
    by_cases hj : β ∈ J.val
    · have hπ := levelProjection_mem_rootAnnihilator fam.connectedReductive fam.maximalSplit D
        fam.generic J.property Tp
      rw [map_sub, (mem_rootAnnihilator _ _).mp hY.1.2.1 β hj,
        (mem_rootAnnihilator _ _).mp hπ β hj, sub_zero]
    · exact (hY.1.2.2 β ⟨hb, hj⟩).le
  have hl := fam.weight_nonneg_of_root_nonneg J hroot α
  have hu := hY.2 α.val (fam.relativeRoots_mem J α)
  rw [map_sub, fam.weight_projectedHeight J, sub_nonneg] at hl
  rw [map_sub, fam.weight_projectedHeight J, sub_nonpos] at hu
  simpa only [fam.weightCoordinate_eq_apply J] using And.intro hl hu

/-- In projected coroot coordinates, the translated split shell fits in the box between the
weights at the two cutoffs. Its Haar volume is bounded by a fixed polynomial of the increment. -/
def CharacteristicSplitVolumeStatement {n : ℕ} (eT : V T ≃ₗ[ℝ] (Fin n → ℝ)) : Prop :=
  (∀ Tp S : V T, MeasurableSet (fam.characteristicSplitHeightRegion J hK Tp S)) ∧
  ∃ A > (0 : ℝ), ∀ da : Measure B, da.IsHaarMeasure →
    ∃ c > (0 : ℝ≥0), ∀ Tp S : V T,
      da (fam.characteristicSplitHeightRegion J hK Tp S) ≤
        (c : ℝ≥0∞) * ∏ α : C, ENNReal.ofReal (fam.weightCoordinate J S α) ∧
      da (fam.characteristicSplitHeightRegion J hK Tp S) ≤
        (c : ℝ≥0∞) * ENNReal.ofReal ((A * (1 + ‖eT S‖)) ^ Fintype.card C)

set_option maxHeartbeats 2200000 in
theorem characteristicSplitVolume {n : ℕ} (eT : V T ≃ₗ[ℝ] (Fin n → ℝ)) :
    fam.CharacteristicSplitVolumeStatement J hK eT := by
  classical
  obtain ⟨e, he, hHaar⟩ := fam.relativeCorootHaar J
  have hHeight (b : B) : H b = ∑ α : C, (e b).toAdd α • (fam.projectedSimpleCoroot J α).val := by
    obtain ⟨t, ht, hl⟩ := (he b).1
    change fam.relativeSplitPoint J b = _ at ht
    change fam.minimalHeight hK (fam.relativeSplitPoint J b) = _
    rw [ht, minimalHeight, fam.minimalHeight_eq_of_torusLog hK _ _ hl]
  have hw (b : B) (α : C) : w α.val (H b) = (e b).toAdd α := by
    rw [hHeight, map_sum]
    simp only [map_smul, fam.weight_projectedSimpleCoroot' J, smul_eq_mul, mul_ite,
      mul_one, mul_zero, Fintype.sum_ite_eq]
  constructor
  · intro Tp S
    have hmem (b : B) : H b ∈ aSpace T J.val ⊓ (D).realCorootSpan := by
      rw [hHeight]
      exact Submodule.sum_mem _ fun α _ => Submodule.smul_mem _ _ (fam.projectedSimpleCoroot J α).property
    have hfun (L : V T →ₗ[ℝ] ℝ) : Continuous fun b : B => L (H b) := by
      simp only [hHeight, map_sum, map_smul, smul_eq_mul]
      exact continuous_finsetSum _ fun α _ =>
        ((continuous_apply α).comp (show Continuous (fun b => (e b).toAdd) from e.continuous)).mul
          continuous_const
    have hset : fam.characteristicSplitHeightRegion J hK Tp S =
        ⋂ α : C, {b | eval T α.val (πJ Tp) < eval T α.val (H b) ∧
          w α.val (H b) ≤ w α.val (πJ (Tp + S))} := by
      ext b
      have hm := hmem b
      change ((H b ∈ (D).realCorootSpan ∧ H b ∈ aSpace T J.val ∧ _) ∧ _) ↔ _
      rw [mem_iInter]
      simp only [Set.mem_ofPred_eq, map_sub, sub_pos, sub_nonpos]
      refine ⟨fun h α => ⟨h.1.2.2 α.val (fam.relativeRoots_mem J α),
        h.2 α.val (fam.relativeRoots_mem J α)⟩, ?_⟩
      intro h
      have ind (β : characterLattice T) (hb : β ∈ Δ \ J.val) : β ∈ fam.relativeSimpleRoots J :=
        Finset.mem_filter.mpr ⟨(mem_simpleFinset fam.connectedReductive fam.maximalSplit).mpr hb.1, hb.2⟩
      exact ⟨⟨hm.2, hm.1, fun β hb => (h ⟨β, ind β hb⟩).1⟩,
        fun β hb => (h ⟨β, ind β hb⟩).2⟩
    rw [hset]
    exact MeasurableSet.iInter fun α =>
      (isOpen_lt continuous_const (hfun (eval T α.val))).measurableSet.inter
        (isClosed_le (hfun (w α.val)) continuous_const).measurableSet
  · let W (α : C) := ((w α.val).comp eT.symm.toLinearMap).toContinuousLinearMap
    let A : ℝ := 1 + ∑ α : C, ‖W α‖
    have hA : 0 < A := by
      have hsum : 0 ≤ ∑ α : C, ‖W α‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
      exact add_pos_of_pos_of_nonneg zero_lt_one hsum
    refine ⟨A, hA, fun da hda => ?_⟩
    obtain ⟨c, hc, hp⟩ := hHaar da hda
    refine ⟨c, hc, fun Tp S => ?_⟩
    let lo (α : C) := fam.weightCoordinate J Tp α
    let hi (α : C) := fam.weightCoordinate J (Tp + S) α
    have hs : fam.characteristicSplitHeightRegion J hK Tp S ⊆ (fun b => (e b).toAdd) ⁻¹' Icc lo hi := by
      intro b hb
      change H b ∈ characteristicSplitShell fam.connectedReductive fam.maximalSplit D J Tp S at hb
      refine ⟨fun α => ?_, fun α => ?_⟩
      · change lo α ≤ (e b).toAdd α
        rw [← hw b α]
        exact (fam.splitShell_weight_bounds J hb α).1
      · change (e b).toAdd α ≤ hi α
        rw [← hw b α]
        exact (fam.splitShell_weight_bounds J hb α).2
    have hwidth (α : C) : hi α - lo α = fam.weightCoordinate J S α := by
      simp only [hi, lo, fam.weightCoordinate_eq_apply J, map_add, add_sub_cancel_left]
    have hbox : da (fam.characteristicSplitHeightRegion J hK Tp S) ≤
        (c : ℝ≥0∞) * ∏ α : C, ENNReal.ofReal (fam.weightCoordinate J S α) := by
      calc
        _ ≤ da ((fun b => (e b).toAdd) ⁻¹' Icc lo hi) := measure_mono hs
        _ = (c : ℝ≥0∞) * ∏ α : C, ENNReal.ofReal (fam.weightCoordinate J S α) := by
          rw [hp.measure_preimage measurableSet_Icc.nullMeasurableSet, Measure.smul_apply,
            Real.volume_Icc_pi, ENNReal.smul_def]
          simp only [hwidth, smul_eq_mul]
    refine ⟨hbox, hbox.trans (mul_le_mul_right ?_ _)⟩
    rw [ENNReal.ofReal_pow (mul_nonneg hA.le (by positivity)), ← Finset.card_univ (α := C),
      ← Finset.prod_const]
    apply Finset.prod_le_prod
    intro α hα
    apply ENNReal.ofReal_le_ofReal
    have hαA : ‖W α‖ ≤ A := by
      have hsum := Finset.single_le_sum (f := fun β : C => ‖W β‖) (fun β _ => norm_nonneg (W β)) hα
      exact hsum.trans (le_add_of_nonneg_left zero_le_one)
    have hval : W α (eT S) = fam.weightCoordinate J S α := by
      simp only [W, LinearMap.coe_toContinuousLinearMap', LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply, fam.weightCoordinate_eq_apply J]
    calc
      _ = W α (eT S) := hval.symm
      _ ≤ ‖W α (eT S)‖ := le_abs_self _
      _ ≤ ‖W α‖ * ‖eT S‖ := (W α).le_opNorm _
      _ ≤ A * (1 + ‖eT S‖) := mul_le_mul hαA (by linarith) (norm_nonneg _) hA.le

end Langlands.Global.StandardParabolicFamily

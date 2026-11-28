import Langlands.Global.RankinSelberg.RealSlotTemperedBound
import Langlands.Global.RankinSelberg.RealUniformTailInclusion
import Langlands.Global.RankinSelberg.RealPrincipalSeriesWhittakerReduction
import Langlands.Representation.Archimedean.RealGenericParameterReduction
import Langlands.Global.RankinSelberg.RealLocalCharacterGrowthInterfaces
import Langlands.Global.RankinSelberg.RealCanonicalWhittakerComparison

/-! # The slot data of a real block list -/

noncomputable section

open Langlands.Archimedean Langlands.LocalFactor.Archimedean
open Langlands.Archimedean.GramFormula
open scoped Manifold ContDiff Matrix.Norms.Operator
open Langlands.Archimedean.RealInducedBlockBound
open Langlands.Archimedean.RealInducedStandardBound
open Langlands.Global.RankinSelbergGlobal.RealGodementProfiles
open Langlands.Global.RankinSelbergGlobal.RealGodement
open Langlands.Global.RankinSelbergGlobal.RealIwasawa

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealLeviStages

variable {r : ℕ}

/-! ## The slots of the induction blocks of nonzero weight -/

/-- The absolute weight of the induction block with first position `p`, and zero if there is
none. -/
def slotWeight (ds : List RealBlock) (p : ℕ) : ℕ :=
  match realInducedBlockAt ds p with
  | some d => d.weight.natAbs
  | none => 0

theorem slotWeight_of {ds : List RealBlock} {p : ℕ} {d : ComplexCharacterData}
    (h : realInducedBlockAt ds p = some d) : slotWeight ds p = d.weight.natAbs := by
  simp [slotWeight, h]

theorem slotWeight_of_none {ds : List RealBlock} {p : ℕ} (h : realInducedBlockAt ds p = none) :
    slotWeight ds p = 0 := by
  simp [slotWeight, h]

theorem exists_of_slotWeight_ne_zero {ds : List RealBlock} {p : ℕ} (h : slotWeight ds p ≠ 0) :
    ∃ d, realInducedBlockAt ds p = some d ∧ slotWeight ds p = d.weight.natAbs := by
  cases hb : realInducedBlockAt ds p with
  | none => exact absurd (slotWeight_of_none hb) h
  | some d => exact ⟨d, rfl, slotWeight_of hb⟩

/-- The slot set of the induction blocks of nonzero weight of a block list of rank `r + 1`. -/
def blockSlots (ds : List RealBlock) (hr : realRank ds = r + 1) : SlotSet (r + 1) where
  starts := (Finset.range (r + 1)).filter fun p => slotWeight ds p ≠ 0
  lt p hp := by
    obtain ⟨d, hd, -⟩ := exists_of_slotWeight_ne_zero (Finset.mem_filter.mp hp).2
    have := realInducedBlockAt_lt hd
    omega
  sep p hp := by
    obtain ⟨d, hd, -⟩ := exists_of_slotWeight_ne_zero (Finset.mem_filter.mp hp).2
    have hnone := (induced_at hd).2.2.2.2.2.2
    intro h
    exact (Finset.mem_filter.mp h).2 (slotWeight_of_none hnone)

theorem mem_blockSlots {ds : List RealBlock} {hr : realRank ds = r + 1} {p : ℕ} :
    p ∈ (blockSlots ds hr).starts ↔ slotWeight ds p ≠ 0 := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, h⟩
    obtain ⟨d, hd, -⟩ := exists_of_slotWeight_ne_zero h
    have := realInducedBlockAt_lt hd
    omega

theorem blockSlots_weight_ne_zero (ds : List RealBlock) (hr : realRank ds = r + 1) :
    ∀ q ∈ (blockSlots ds hr).starts, slotWeight ds q ≠ 0 :=
  fun _ hq => mem_blockSlots.mp hq

/-! ## The exponents of the positions -/

theorem realPositionExponent_expand (ds : List RealBlock) (i : ℕ) :
    realPositionExponent (RealPrincipalSeries.expand ds) i = realPositionExponent ds i := by
  induction ds generalizing i with
  | nil => rfl
  | cons d ds ih =>
    rw [show d :: ds = [d] ++ ds from rfl, RealJacquet.expand_append']
    cases d with
    | character c =>
      rcases i with _ | i
      · rfl
      · exact ih i
    | induced d =>
      rw [RealJacquet.expand_induced_single]
      rcases i with _ | _ | i
      · rfl
      · rfl
      · exact ih i

theorem realPositionBlockExponent_eq_zero :
    ∀ (ds : List RealBlock), (∀ d ∈ ds, realBlockExponent d = 0) →
      ∀ i, realPositionBlockExponent ds i = 0
  | [], _, _ => rfl
  | .character _ :: _, h, 0 => h _ List.mem_cons_self
  | .character _ :: ds, h, i + 1 =>
      realPositionBlockExponent_eq_zero ds (fun d hd => h d (List.mem_cons_of_mem _ hd)) i
  | .induced _ :: _, h, 0 => h _ List.mem_cons_self
  | .induced _ :: _, h, 1 => h _ List.mem_cons_self
  | .induced _ :: ds, h, i + 2 =>
      realPositionBlockExponent_eq_zero ds (fun d hd => h d (List.mem_cons_of_mem _ hd)) i

theorem not_induced_pred {ds : List RealBlock} {p : ℕ} {d : ComplexCharacterData}
    (hd : realInducedBlockAt ds (p + 1) = some d) : realInducedBlockAt ds p = none := by
  cases hb : realInducedBlockAt ds p with
  | none => rfl
  | some d' =>
    have := (induced_at hb).2.2.2.2.2.2
    rw [this] at hd
    exact absurd hd (by simp)

/-- **The real parts of the position exponents** of a block list with imaginary block
exponents are the half weights `±|k|/2` on the slots of the induction blocks of nonzero weight
`k`, and zero elsewhere. -/
theorem realPositionExponent_re (ds : List RealBlock) (hr : realRank ds = r + 1)
    (him : ∀ d ∈ ds, realBlockExponent d = 0) (i : Fin (r + 1)) :
    (realPositionExponent ds i).re = halfWeights (blockSlots ds hr) (slotWeight ds) i := by
  have hz := realPositionBlockExponent_eq_zero ds him
  simp only [halfWeights, SlotSet.slotVec, mem_blockSlots]
  by_cases hA : ∃ p d, realInducedBlockAt ds p = some d ∧ ((i : ℕ) = p ∨ (i : ℕ) = p + 1)
  · obtain ⟨p, d, hd, hi⟩ := hA
    obtain ⟨-, -, he1, he2, hb1, hb2, hnone⟩ := induced_at hd
    have hre0 : d.exponent.re = 0 := by rw [← hb1]; exact hz p
    have hw := slotWeight_of hd
    rcases hi with hi | hi
    · rw [hi, he1, hw]
      have hpred : ¬ ((p ≠ 0) ∧ slotWeight ds (p - 1) ≠ 0) := by
        rintro ⟨hp0, hp1⟩
        obtain ⟨d', hd', -⟩ := exists_of_slotWeight_ne_zero hp1
        have : realInducedBlockAt ds (p - 1 + 1) = some d := by
          rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hp0)]; exact hd
        rw [not_induced_pred this] at hd'
        exact absurd hd' (by simp)
      by_cases hk : d.weight.natAbs = 0
      · simp only [hk, ne_eq, not_true_eq_false, ite_false]
        rw [ite_eq_right (by simpa [hk] using hpred)]
        simp [hre0]
      · simp only [hk, ne_eq, not_false_eq_true, ite_true]
        simp [hre0]
    · rw [hi, he2, slotWeight_of_none hnone]
      simp only [ne_eq, not_true_eq_false, ite_false, Nat.add_sub_cancel, hw]
      by_cases hk : d.weight.natAbs = 0
      · simp [hk, hre0]
      · simp [hk, hre0]
  · push Not at hA
    have hre := exponent_re_eq ds i (fun p d hd => hA p d hd)
    rw [hre, hz]
    have h1 : ¬ slotWeight ds i ≠ 0 := by
      intro h
      obtain ⟨d, hd, -⟩ := exists_of_slotWeight_ne_zero h
      exact (hA _ d hd).1 rfl
    have h2 : ¬ ((i : ℕ) ≠ 0 ∧ slotWeight ds ((i : ℕ) - 1) ≠ 0) := by
      rintro ⟨h0, h⟩
      obtain ⟨d, hd, -⟩ := exists_of_slotWeight_ne_zero h
      exact (hA _ d hd).2 (by omega)
    rw [ite_eq_right h1, ite_eq_right h2]

/-- The slot differences of the position exponents are the absolute weights. -/
theorem realPositionExponent_slot (ds : List RealBlock) (hr : realRank ds = r + 1) :
    ∀ q (hq : q ∈ (blockSlots ds hr).starts),
      realPositionExponent ds (SlotSet.first hq : ℕ) -
        realPositionExponent ds (SlotSet.second hq : ℕ) = (slotWeight ds q : ℂ) := by
  intro q hq
  obtain ⟨d, hd, hw⟩ := exists_of_slotWeight_ne_zero (mem_blockSlots.mp hq)
  obtain ⟨-, -, he1, he2, -⟩ := induced_at hd
  change realPositionExponent ds q - realPositionExponent ds (q + 1) = _
  rw [he1, he2, hw]
  ring

/-! ## The admissible modes of the standard vectors -/

set_option backward.isDefEq.respectTransparency false in
/-- **The standard vectors have only admissible modes** on the slots of the induction blocks of
nonzero weight. -/
theorem slotModes_of_mem (ds : List RealBlock) (hr : realRank ds = r + 1)
    {f : Langlands.GeneralLinear (r + 1) ℝ → ℂ}
    (hf : f ∈ Automorphic.realStandardKFinite (r + 1) ds) :
    SlotModes (slotsOf (blockSlots ds hr) (slotWeight ds)) f := by
  obtain ⟨D, hD⟩ := exists_hasDegree hf.1.1.1.continuous hf.2 (slots ds (r + 1))
  have hIC := inClass_slots hf hD
  intro t ht j hj k _
  obtain ⟨htp, htM⟩ := mem_mkSlots ht
  have htS : t.p ∈ (blockSlots ds hr).starts := by
    rw [← startList_toFinset]
    exact List.mem_toFinset.mpr htp
  obtain ⟨d, hd, hw⟩ := exists_of_slotWeight_ne_zero (mem_blockSlots.mp htS)
  have hs := mkSlot_mem_slots (N := r + 1) hd t.hp
  have hM : (mkSlot ds (r + 1) t.p t.hp d).M = t.M := by
    rw [htM, hw]
    rfl
  have h := (hIC.2.2 _ hs).2.1 j (by rw [hM]; exact hj) k
  exact h

/-! ## The tempered bound on the descending canonical range -/

/-- The descending expansion of a block list of rank `r + 1` is a character list. -/
theorem exists_expand_eq_characterList (ds : List RealBlock) (hr : realRank ds = r + 1) :
    ∃ (p : Fin (r + 1) → Fin 2) (z : Fin (r + 1) → ℂ),
      RealPrincipalSeries.expand ds = RealGodementProfiles.characterList p z := by
  obtain ⟨cs, hcs⟩ := RealJacquet.isRealCharacterList_expand ds
  have hrank : realRank (cs.map RealBlock.character) = r + 1 := by
    rw [← hcs, RealPrincipalSeries.realRank_expand, hr]
  obtain ⟨p, z, hpz⟩ := RealPrincipalSeries.exists_characterList_of_map_character cs hrank
  exact ⟨p, z, hcs.trans hpz⟩

/-- **The tempered bound on the descending canonical range.** Let `ds` be a block list of rank
`r + 1` with imaginary block exponents whose descending expansion is the character list of
`p, z`. Every function in the range of the canonical Jacquet map of `p, z` restricted to the
standard vectors of `ds` satisfies the half-modulus bound with arbitrarily small exponential
loss. -/
theorem temperedBound_of_mem_range (ds : List RealBlock) (hr : realRank ds = r + 1)
    (him : ∀ d ∈ ds, realBlockExponent d = 0) (a : ℝˣ) (p : Fin (r + 1) → Fin 2)
    (z : Fin (r + 1) → ℂ) (he : RealPrincipalSeries.expand ds = characterList p z)
    (h : Automorphic.realStandardKFinite (r + 1) ds ≤
      Automorphic.realStandardKFinite (r + 1) (characterList p z))
    {W : Langlands.GeneralLinear (r + 1) ℝ → ℂ}
    (hW : W ∈ ((canonicalJacquetMap a p z).comp (Submodule.inclusion h)).range) (ε : ℝ)
    (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (y : Fin (r + 1) → ℝ) (k : unitaryCompact ℝ (r + 1)),
      ‖W (RealIwasawa.torus y * k.val)‖ ≤
        C * Real.exp (torusModularLog (r + 1) y / 2 + ε * ∑ i, |y i|) := by
  obtain ⟨f, rfl⟩ := hW
  set g := Submodule.inclusion h f
  have hzi : ∀ i : Fin (r + 1), z i = realPositionExponent ds i := by
    intro i
    rw [← realPositionExponent_characterList p z i, ← he, realPositionExponent_expand]
  have hz : ∀ q (hq : q ∈ (blockSlots ds hr).starts),
      z (SlotSet.first hq) - z (SlotSet.second hq) = slotWeight ds q := by
    intro q hq
    rw [hzi, hzi]
    exact realPositionExponent_slot ds hr q hq
  have hre : ∀ i, (z i).re = halfWeights (blockSlots ds hr) (slotWeight ds) i := by
    intro i
    rw [hzi]
    exact realPositionExponent_re ds hr him i
  have hφ := isCompactProfile_compactRestriction g.property
  have hmodes : SlotModes (slotsOf (blockSlots ds hr) (slotWeight ds))
      (standardSection z (compactRestriction (g : Langlands.GeneralLinear (r + 1) ℝ → ℂ))) := by
    rw [standardSection_compactRestriction g.property]
    exact slotModes_of_mem ds hr f.property
  exact canonical_tempered_slot_bound (blockSlots ds hr) hφ (slotWeight ds)
    (blockSlots_weight_ne_zero ds hr) hz hre hmodes a ε hε

end Langlands.Global.RankinSelbergGlobal.RealLeviStages

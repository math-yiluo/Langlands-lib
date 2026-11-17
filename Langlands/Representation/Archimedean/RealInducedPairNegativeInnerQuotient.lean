import Langlands.Representation.Archimedean.RealCharacterWindowProjection
import Langlands.Representation.Archimedean.RealInducedPairQuotientPresentation
import Langlands.Representation.Archimedean.RealInducedPairLinkedReplacement

/-! # A middle induced block surjects onto a linked pair with negative inner weight -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

namespace RealInducedPairNegativeInnerQuotient

open RealCharacterPair RealCharacterPairReducible RealBlockFrobeniusMap
open RealBlockPosition RealStandardFiltration RealCharacterWindowProjection
open RealInducedPairLinkedReplacement RealInducedPairQuotientPresentation
open RealStrictCharacterLanglandsQuotient RealAdjacentWindowSpanning

/-- A choice of left-pair parity that gives the middle pair the inner-block signs. -/
def leftParity (d e : ComplexCharacterData) (k : ℕ) : Fin 2 :=
  ⟨((innerWeight d e k).natAbs + d.weight.natAbs) % 2, Nat.mod_lt _ two_pos⟩

abbrev u (d e : ComplexCharacterData) (k : ℕ) := lo d (leftParity d e k)
abbrev v (d e : ComplexCharacterData) (k : ℕ) := hi d (leftParity d e k)
abbrev x (e : ComplexCharacterData) := lo e 0
abbrev y (e : ComplexCharacterData) := hi e 0

/-- The positive-weight induction datum for the descending central endpoint pair. -/
def middleData (d e : ComplexCharacterData) (k : ℕ) : ComplexCharacterData :=
  pairInduced (x e) (v d e k) (innerWeight d e k).natAbs

/-- The actual standard module with one central induction block. -/
def middleList (d e : ComplexCharacterData) (k : ℕ) : List RealBlock :=
  [.character (u d e k), .induced (middleData d e k), .character (y e)]

section Arithmetic

variable {d e : ComplexCharacterData} {k : ℕ}
  (hlink : IsLinkedAt d e k) (hneg : innerWeight d e k < 0)

include hneg in
theorem cutoff_bounds :
    0 < (innerWeight d e k).natAbs ∧
      (innerWeight d e k).natAbs < d.weight.natAbs ∧
      (innerWeight d e k).natAbs < e.weight.natAbs := by
  have hc : ((innerWeight d e k).natAbs : ℤ) = -innerWeight d e k := by
    rw [Int.natCast_natAbs, abs_of_neg hneg]
  have hm0 := min_le_left d.weight.natAbs e.weight.natAbs
  have hm1 := min_le_right d.weight.natAbs e.weight.natAbs
  dsimp [innerWeight] at hc hneg ⊢
  omega

theorem middle_parity :
    Even (((innerWeight d e k).natAbs : ℤ) - 1 - pairParity (v d e k) (x e)) := by
  rw [Int.even_iff]
  dsimp [pairParity, v, x, hi, lo, leftParity, RealJacquetFrobenius.charData]
  omega

theorem v_parity : (v d e k).parity =
    ⟨((innerWeight d e k).natAbs + 1) % 2, Nat.mod_lt _ two_pos⟩ := by
  apply Fin.ext
  dsimp [v, hi, leftParity, RealJacquetFrobenius.charData]
  omega

include hlink hneg in
theorem middle_gap :
    (v d e k).exponent - (x e).exponent = ((innerWeight d e k).natAbs : ℂ) := by
  obtain ⟨_, _, h3, h4⟩ := endpoint_equalities hlink
  have hc : ((innerWeight d e k).natAbs : ℂ) = -(innerWeight d e k : ℂ) := by
    have hi : ((innerWeight d e k).natAbs : ℤ) = -innerWeight d e k := by
      rw [Int.natCast_natAbs, abs_of_neg hneg]
    simpa only [Int.cast_natCast, Int.cast_neg] using
      congrArg (fun t : ℤ => (t : ℂ)) hi
  change (d.exponent + (d.weight.natAbs : ℂ) / 2) -
    (e.exponent - (e.weight.natAbs : ℂ) / 2) = _
  linear_combination h3 - h4 - hc

include hlink hneg in
theorem middle_first_exponent :
    (middleData d e k).exponent + ((middleData d e k).weight.natAbs : ℂ) / 2 =
      (v d e k).exponent := by
  have hg := middle_gap hlink hneg
  simp only [middleData, pairInduced_exponent, pairInduced_weight, Int.natAbs_natCast]
  linear_combination -hg / 2

include hlink hneg in
theorem middle_second_exponent :
    (middleData d e k).exponent - ((middleData d e k).weight.natAbs : ℂ) / 2 =
      (x e).exponent := by
  have hg := middle_gap hlink hneg
  simp only [middleData, pairInduced_exponent, pairInduced_weight, Int.natAbs_natCast]
  linear_combination hg / 2

include hlink hneg in
theorem position_characters :
    realPositionCharacter (middleList d e k) =
      realPositionCharacter (X d e (leftParity d e k) 0) := by
  funext i z
  rw [realPositionCharacter_eq_charFun, realPositionCharacter_eq_charFun]
  rcases i with _ | _ | _ | _ | i
  · rfl
  · change RealJacquetFrobenius.charFun
      ⟨((middleData d e k).weight.natAbs + 1) % 2, _⟩
      ((middleData d e k).exponent + ((middleData d e k).weight.natAbs : ℂ) / 2) z =
        RealJacquetFrobenius.charFun (v d e k).parity (v d e k).exponent z
    rw [middle_first_exponent hlink hneg, v_parity]
    simp only [middleData, pairInduced_weight, Int.natAbs_natCast]
  · change RealJacquetFrobenius.charFun 0
      ((middleData d e k).exponent - ((middleData d e k).weight.natAbs : ℂ) / 2) z =
        RealJacquetFrobenius.charFun 0 (x e).exponent z
    rw [middle_second_exponent hlink hneg]
  · rfl
  · rfl

end Arithmetic

section Maps

variable {d e : ComplexCharacterData} {k : ℕ}
  (hlink : IsLinkedAt d e k) (hneg : innerWeight d e k < 0)

include hlink hneg in
theorem middle_le :
    KF 4 (middleList d e k) ≤ KF 4 (X d e (leftParity d e k) 0) := by
  intro f hf
  refine ⟨?_, hf.2⟩
  have hchars : IsCharacterList (X d e (leftParity d e k) 0) := by
    intro b hb
    simp only [X, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩
  rw [realStandardModule_eq hchars, ← position_characters hlink hneg]
  exact hf.1.1

/-- The actual inclusion into the four-character module. -/
def middleInclusion : KF 4 (middleList d e k) →ₗ[ℂ] KF 4 (X d e (leftParity d e k) 0) :=
  Submodule.inclusion (middle_le hlink hneg)

theorem middleInclusion_exact :
    IsRealIntertwinerModulo 4 (middleList d e k) (X d e (leftParity d e k) 0) ⊥
      (middleInclusion hlink hneg) := by
  refine ⟨fun κ f => ⟨rightTranslation_mem_kFiniteFunctions_realStandardModule _ _ f.2 κ.2,
    rightTranslation_mem_kFiniteFunctions_realStandardModule _ _ (middleInclusion hlink hneg f).2 κ.2,
    ?_⟩,
    fun A f => ⟨rightDerivative_mem_kFiniteFunctions_realStandardModule _ _ f.2 A,
      rightDerivative_mem_kFiniteFunctions_realStandardModule _ _
        (middleInclusion hlink hneg f).2 A, ?_⟩⟩ <;>
    rw [Submodule.mem_bot, sub_eq_zero] <;> rfl

include hlink hneg in
theorem high_mem_middle (f : KF 4 (X d e (leftParity d e k) 0)) :
    (highMiddle (u d e k) (v d e k) (x e) (y e) (innerWeight d e k).natAbs f :
      Langlands.GeneralLinear 4 ℝ → ℂ) ∈ KF 4 (middleList d e k) := by
  let Q := highMiddle (u d e k) (v d e k) (x e) (y e) (innerWeight d e k).natAbs
  refine ⟨mem_realStandardModule_of_unitaryCompact (N := 4) (ds := middleList d e k)
    rfl ?_ ?_, (Q f).2.2⟩
  · rw [position_characters hlink hneg]
    exact (Q f).2.1.1
  · intro p c hc j hj g hg
    rcases p with _ | _ | _ | _ | p <;> simp [middleList, realInducedBlockAt] at hc
    subst c
    have hj' : |j| < ((innerWeight d e k).natAbs : ℤ) := by
      simpa only [middleData, pairInduced_weight, Int.abs_eq_natAbs, Int.natAbs_natCast] using hj
    calc
      _ = highMultiplier (innerWeight d e k).natAbs j *
          blockFourierCoefficient 4 1 j f g :=
        high_fourier (n := 4) (pre := [.character (u d e k)])
          (post := [.character (y e)]) (c := v d e k) (d := x e)
          rfl (cutoff_bounds hneg).1 middle_parity f j hg
      _ = 0 := by
        simp only [highMultiplier, lowMultiplier, ite_eq_left hj', sub_self, zero_mul]

/-- Restrict the published two-block quotient to the actual middle-induced submodule. -/
def quotient : KF 4 (middleList d e k) →ₗ[ℂ] KF 4 [.induced d, .induced e] :=
  (quotientMap d e (leftParity d e k) 0
    (lt_trans (cutoff_bounds hneg).1 (cutoff_bounds hneg).2.1)
    (lt_trans (cutoff_bounds hneg).1 (cutoff_bounds hneg).2.2)).comp
      (middleInclusion hlink hneg)

theorem quotient_exact :
    IsRealIntertwinerModulo 4 (middleList d e k) [.induced d, .induced e] ⊥
      (quotient hlink hneg) :=
  modulo_comp_bot (RealInducedPairQuotientPresentation.quotient_exact d e (leftParity d e k) 0 _ _)
    (middleInclusion_exact hlink hneg)

theorem quotient_surjective : Function.Surjective (quotient hlink hneg) := by
  let sd := leftParity d e k
  let L := d.weight.natAbs
  let h := (innerWeight d e k).natAbs
  have hd : 0 < d.weight.natAbs := lt_trans (cutoff_bounds hneg).1 (cutoff_bounds hneg).2.1
  have he : 0 < e.weight.natAbs := lt_trans (cutoff_bounds hneg).1 (cutoff_bounds hneg).2.2
  let T := quotientMap d e sd 0 hd he
  let P := lowLeft (u d e k) (v d e k) (x e) (y e) L
  let Q := highMiddle (u d e k) (v d e k) (x e) (y e) h
  have hspan : LinearMap.range P ⊔ LinearMap.range Q = ⊤ :=
    four_spanning _ _ _ _ L h hd (cutoff_bounds hneg).1 (cutoff_bounds hneg).2.1
      (pair_parity d sd) middle_parity
  have hkill : ∀ a, T (P a) = 0 := by
    intro a
    apply LinearMap.mem_ker.mp
    rw [ker_quotient d e sd 0 hd he]
    apply Submodule.mem_sup_left
    exact ⟨blockFrobMap (dataBd d e sd 0) a, rfl⟩
  intro z
  obtain ⟨f, rfl⟩ := RealInducedPairQuotientPresentation.quotient_surjective d e sd 0 hd he z
  have hf : f ∈ LinearMap.range P ⊔ LinearMap.range Q := by rw [hspan]; trivial
  obtain ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hf
  refine ⟨⟨(Q b : Langlands.GeneralLinear 4 ℝ → ℂ), high_mem_middle hlink hneg b⟩, ?_⟩
  change T (Q b) = T (P a + Q b)
  rw [map_add, hkill, zero_add]

end Maps
end RealInducedPairNegativeInnerQuotient

/-- For linked data with negative signed inner weight, the actual module with the central
inner induction block admits a surjective exact intertwiner onto the original two blocks. -/
def RealInducedPairNegativeInnerQuotientStatement : Prop :=
  ∀ (d e : ComplexCharacterData) (k : ℕ),
    RealInducedPairLinkedReplacement.IsLinkedAt d e k →
    RealInducedPairLinkedReplacement.innerWeight d e k < 0 →
    ∃ T : RealStandardFiltration.KF 4 (RealInducedPairNegativeInnerQuotient.middleList d e k) →ₗ[ℂ]
      RealStandardFiltration.KF 4 [.induced d, .induced e],
      IsRealIntertwinerModulo 4 (RealInducedPairNegativeInnerQuotient.middleList d e k)
        [.induced d, .induced e] ⊥ T ∧ Function.Surjective T

theorem realInducedPairNegativeInnerQuotient : RealInducedPairNegativeInnerQuotientStatement :=
  fun _ _ _ hlink hneg =>
    ⟨RealInducedPairNegativeInnerQuotient.quotient hlink hneg,
      RealInducedPairNegativeInnerQuotient.quotient_exact hlink hneg,
      RealInducedPairNegativeInnerQuotient.quotient_surjective hlink hneg⟩

end Langlands.Archimedean

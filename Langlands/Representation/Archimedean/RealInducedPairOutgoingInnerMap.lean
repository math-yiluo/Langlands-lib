import Langlands.Representation.Archimedean.RealInducedPairOutgoingInnerWindow
import Langlands.Representation.Archimedean.RealCharacterInducedSwap

/-! # The actual mixed inner target of the outgoing linked crossings -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

namespace RealInducedPairOutgoingInnerMap

open RealBlockFrobeniusMap RealBlockMultiplier RealBlockPosition RealBlockJacquet
open RealInducedPairFrobenius RealInducedPairLinkedReplacement
open RealInducedPairLinkedIncoming RealInducedPairIncomingKernel
open RealStandardFiltration

/-- The actual inner induction block between the two outer endpoint characters. -/
abbrev innerList (d e : ComplexCharacterData) (k : ℕ) : List RealBlock :=
  [.character (first e), .induced (innerData d e k), .character (second d)]

section Endpoint

variable {d e : ComplexCharacterData} {k : ℕ}
  (h : IsLinkedAt d e k)
  (hp : Even ((outerWeight d e k : ℤ) - (e.weight.natAbs : ℤ)))
  (hq : innerWeight d e k < 0)

include h hq in
theorem inner_first_exponent :
    (innerData d e k).exponent + ((innerData d e k).weight.natAbs : ℂ) / 2 =
      (first d).exponent := by
  have hc : ((innerWeight d e k).natAbs : ℂ) = -(innerWeight d e k : ℂ) := by
    simpa only [Int.cast_natCast, Int.cast_neg] using
      congrArg (fun z : ℤ => (z : ℂ))
        (show ((innerWeight d e k).natAbs : ℤ) = -innerWeight d e k by
          rw [Int.natCast_natAbs, abs_of_neg hq])
  change innerExponent d e + ((innerWeight d e k).natAbs : ℂ) / 2 =
    d.exponent + (d.weight.natAbs : ℂ) / 2
  rw [hc]
  linear_combination (endpoint_equalities h).2.2.2

include h hq in
theorem inner_second_exponent :
    (innerData d e k).exponent - ((innerData d e k).weight.natAbs : ℂ) / 2 =
      (second e).exponent := by
  have hc : ((innerWeight d e k).natAbs : ℂ) = -(innerWeight d e k : ℂ) := by
    simpa only [Int.cast_natCast, Int.cast_neg] using
      congrArg (fun z : ℤ => (z : ℂ))
        (show ((innerWeight d e k).natAbs : ℤ) = -innerWeight d e k by
          rw [Int.natCast_natAbs, abs_of_neg hq])
  change innerExponent d e - ((innerWeight d e k).natAbs : ℂ) / 2 =
    e.exponent - (e.weight.natAbs : ℂ) / 2
  rw [hc]
  linear_combination (endpoint_equalities h).2.2.1

include hp hq in
theorem inner_first_sign :
    ((innerData d e k).weight.natAbs + 1) % 2 = (d.weight.natAbs + 1) % 2 := by
  have hs := weight_sum d e k
  have hc : ((innerWeight d e k).natAbs : ℤ) = -innerWeight d e k := by
    rw [Int.natCast_natAbs, abs_of_neg hq]
  simp only [innerData, characterOfParams_weight]
  rw [Int.even_iff] at hp
  omega

include h hp hq in
theorem posChar_inner :
    realPositionCharacter (innerList d e k) = realPositionCharacter (l3 d e) := by
  funext i x
  rw [realPositionCharacter_eq_charFun, realPositionCharacter_eq_charFun]
  rcases i with _ | _ | _ | _ | i
  · rfl
  · change RealJacquetFrobenius.charFun
      ⟨((innerData d e k).weight.natAbs + 1) % 2, _⟩
      ((innerData d e k).exponent + ((innerData d e k).weight.natAbs : ℂ) / 2) x =
        RealJacquetFrobenius.charFun
          ⟨(d.weight.natAbs + 1) % 2, _⟩ (first d).exponent x
    rw [inner_first_exponent h hq]
    congr 2
    exact inner_first_sign hp hq
  · change RealJacquetFrobenius.charFun 0
      ((innerData d e k).exponent - ((innerData d e k).weight.natAbs : ℂ) / 2) x =
        RealJacquetFrobenius.charFun 0 (second e).exponent x
    rw [inner_second_exponent h hq]
  · rfl
  · rfl

include h hp hq in
/-- The central high window is the Fourier condition for the actual inner block. -/
theorem mem_inner (f : KF (l3 d e))
    (hf : ∀ g ∈ unitaryCompact ℝ 4, ∀ j : ℤ,
      |j| < (innerWeight d e k).natAbs →
        blockFourierCoefficient 4 1 j (f : Langlands.GeneralLinear 4 ℝ → ℂ) g = 0) :
    (f : Langlands.GeneralLinear 4 ℝ → ℂ) ∈ KF (innerList d e k) := by
  refine ⟨mem_realStandardModule_of_unitaryCompact (N := 4)
    (ds := innerList d e k) rfl ?_ ?_, f.2.2⟩
  · rw [posChar_inner h hp hq]
    exact f.2.1.1
  · intro p x hx j hj g hg
    rcases p with _ | _ | _ | _ | p <;> simp [realInducedBlockAt] at hx
    subst x
    apply hf g hg j
    simpa only [innerData, characterOfParams_weight, Int.abs_eq_natAbs] using hj

end Endpoint

section Exact

variable {d e : ComplexCharacterData} {μ₁ μ₀ μ₂ μ₃ : ℤ → ℂ}
  (hdata : MultiplierData d e (swapParameter d e) μ₁ μ₀ μ₂ μ₃)

include hdata

/-- The first three crossings already intertwine on the full-character target. -/
theorem to3_exact :
    IsRealIntertwinerModulo 4 (src d e) (l3 d e) ⊥ hdata.to3 := by
  have h1 : IsRealIntertwinerModulo 4 (l0 d e) (l1 d e) ⊥
      (blockFrobMap hdata.data1) := by
    refine isRealIntertwinerModulo_blockFrobMap hdata.data1 ?_ ⊥
    convert hdata.rec1 using 1
    dsimp [GramFormula.realPositionExponent, first, second,
      RealJacquetFrobenius.charData, swapParameter]
    ring
  have h0 : IsRealIntertwinerModulo 4 (l1 d e) (l10 d e) ⊥
      (blockFrobMap hdata.data0) := by
    refine isRealIntertwinerModulo_blockFrobMap hdata.data0 ?_ ⊥
    convert hdata.rec0 using 1
    dsimp [GramFormula.realPositionExponent, first, second,
      RealJacquetFrobenius.charData, swapParameter]
    ring
  have h2 : IsRealIntertwinerModulo 4 (l10 d e) (l3 d e) ⊥
      (blockFrobMap hdata.data20) := by
    refine isRealIntertwinerModulo_blockFrobMap hdata.data20 ?_ ⊥
    convert hdata.rec2 using 1
    dsimp [GramFormula.realPositionExponent, first, second,
      RealJacquetFrobenius.charData, swapParameter]
    ring
  exact modulo_comp_bot h2
    (modulo_comp_bot h0 (modulo_comp_bot h1 (inclusion_intertwiner d e)))

end Exact

section Map

variable {d e : ComplexCharacterData} {k : ℕ}
  (h : IsLinkedAt d e k)
  (hp : Even ((outerWeight d e k : ℤ) - (e.weight.natAbs : ℤ)))
  (hq : innerWeight d e k < 0)
  {μ₀ μ₂ : ℤ → ℂ}
  (hdata : MultiplierData d e (swapParameter d e)
    (signedMultiplier (-(outerWeight d e k : ℤ)) (e.weight.natAbs + 1))
    μ₀ μ₂ (signedMultiplier (-innerWeight d e k) (d.weight.natAbs + 1)))

/-- The outgoing three-crossing map with its actual mixed inner target. -/
def innerMap : KF (src d e) →ₗ[ℂ] KF (innerList d e k) :=
  LinearMap.codRestrict (KF (innerList d e k)) ((KF (l3 d e)).subtype.comp hdata.to3)
    (fun f => mem_inner h hp hq (hdata.to3 f)
      ((RealInducedPairOutgoingInnerWindow.negative_inner_window hp hdata hq).2 f))

include h hp hq hdata

theorem innerMap_exact :
    IsRealIntertwinerModulo 4 (src d e) (innerList d e k) ⊥
      (innerMap h hp hq hdata) :=
  RealCharacterInducedSwap.modulo_bot_of_coe (to3_exact hdata) (fun _ => rfl)

variable
  (hn0 : ∀ j : ℤ, Even (j - ((d.weight.natAbs + e.weight.natAbs + 2 : ℕ) : ℤ)) →
    μ₀ j ≠ 0)
  (hn2 : ∀ j : ℤ, Even j → μ₂ j ≠ 0)

include hn0 hn2

/-- The actual inner map has precisely the same kernel as the actual outer tail. -/
theorem innerMap_eq_zero_iff (f : KF (src d e)) :
    innerMap h hp hq hdata f = 0 ↔ RealInducedPairOuterTail.outerMap h hp f = 0 := by
  have hthree : innerMap h hp hq hdata f = 0 ↔ hdata.to3 f = 0 := by
    constructor <;> intro hf <;> apply Subtype.ext
    · exact congrArg (fun z : KF (innerList d e k) =>
        (z : Langlands.GeneralLinear 4 ℝ → ℂ)) hf
    · exact congrArg (fun z : KF (l3 d e) =>
        (z : Langlands.GeneralLinear 4 ℝ → ℂ)) hf
  have hfirst : hdata.to3 f = 0 ↔ hdata.to1 f = 0 := by
    change f ∈ LinearMap.ker hdata.to3 ↔ f ∈ LinearMap.ker hdata.to1
    rw [RealInducedPairIncomingLift.ker_to3_eq_ker_to1 hdata hn0 hn2]
  have hp1 : Even (-(outerWeight d e k : ℤ) - 1 -
      ((e.weight.natAbs + 1 : ℕ) : ℤ)) := by
    rw [Int.even_iff] at hp ⊢
    omega
  have htail := RealInducedPairKernelRecovery.blockFrobMap_eq_zero_iff_tail
    hdata.data1 (outerWeight d e k) (by rw [Int.even_iff] at hp1 ⊢; omega)
    (fun j hj => by
      simpa only [Int.natAbs_neg, Int.natAbs_natCast] using
        (signedMultiplier_neg (by
          have := RealInducedPairOuterTail.outerWeight_pos d e k
          omega) hp1 hj))
    (Submodule.inclusion (src_le_l0 d e) f)
  rw [hthree, hfirst, RealInducedPairOuterTail.outerMap_eq_zero_iff h hp f]
  exact htail

theorem ker_innerMap :
    LinearMap.ker (innerMap h hp hq hdata) =
      LinearMap.ker (RealInducedPairOuterTail.outerMap h hp) := by
  ext f
  exact innerMap_eq_zero_iff h hp hq hdata hn0 hn2 f

end Map

end RealInducedPairOutgoingInnerMap

open RealInducedPairFrobenius RealInducedPairLinkedReplacement
  RealInducedPairOutgoingInnerMap in
/-- At negative signed inner weight the outgoing map has an actual mixed inner
target and the same kernel as the actual outer tail. -/
def RealInducedPairOutgoingInnerMapStatement : Prop :=
  ∀ (d e : ComplexCharacterData) (k : ℕ) (h : IsLinkedAt d e k)
    (hp : Even ((outerWeight d e k : ℤ) - (e.weight.natAbs : ℤ))),
    innerWeight d e k < 0 →
    ∃ T : KF (src d e) →ₗ[ℂ] KF (innerList d e k),
      IsRealIntertwinerModulo 4 (src d e) (innerList d e k) ⊥ T ∧
      LinearMap.ker T = LinearMap.ker (RealInducedPairOuterTail.outerMap h hp)

open RealInducedPairOutgoingInnerMap in
theorem realInducedPairOutgoingInnerMap :
    RealInducedPairOutgoingInnerMapStatement := by
  intro d e k h hp hq
  obtain ⟨μ₀, μ₂, hdata, hn0, hn2⟩ :=
    RealInducedPairOutgoingInnerWindow.exists_multiplierData h hp
  exact ⟨innerMap h hp hq hdata, innerMap_exact h hp hq hdata,
    ker_innerMap h hp hq hdata hn0 hn2⟩

end Langlands.Archimedean

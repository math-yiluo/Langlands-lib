import Langlands.Representation.Archimedean.RealCompactParityLifting
import Langlands.Representation.Archimedean.RealInducedPairPositiveTwoPrefix

/-! # The linked positive-inner filtration for two induction blocks -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealInducedPairPositiveFiltration

open Langlands.LocalFactor.Archimedean RealStandardFiltration RealBlockFrobeniusMap
open RealInducedPairLinkedReplacement RealInducedPairAscendingExchange
open RealBlockJacquet RealBlockFrobeniusDisjoint RealBlockFourierFinite
open RealCharacterPair RealCharacterPairReducible
open RealStrictCharacterLanglandsQuotient (IsCharacterList)
open RealInducedPairPositiveOppositeOuter (flipParity)

namespace G
export RealInducedPairPositiveGenericMiddle
  (source swapped sectionMap middle middleData parity parity_eq middle_coeff exists_split
    quotient_eq_iff doubleCoeff modeSign pairSign flipParity_ne_self)
end G

namespace P
export RealInducedPairQuotientPresentation (lo hi X quotientMap quotient_section ker_tail_eq_range)
end P

namespace C
export RealInducedPairPositiveCrossedQuotient
  (quotient cutoff cutoff_pos middle_parity tail_zero_of_low)
end C

namespace M
export RealInducedPairCrossedMiddleQuotient (leftParity rightParity)
end M

namespace F
export RealInducedPairPositiveTwoPrefix
  (totalPrefix oppositePrefix absorption_iff_ker_le filtration)
end F

namespace D
export RealInducedPairDistantParity (innerBinomial inner_difference inner_parity)
end D

local notation "Φ" => blockFourierCoefficient
local notation "G₄" => Langlands.GeneralLinear 4 ℝ
local notation "K₄" => unitaryCompact ℝ 4

variable {d e : ComplexCharacterData} {k : ℕ}

local notation "sd" => M.leftParity d
local notation "se" => M.rightParity d e k
local notation "H" => C.cutoff d e k

private theorem character_neg_of_sum (c c' : RealCharacterData)
    (h : c.parity.val + c'.parity.val = 1) :
    (c'.character (-1) : ℂ) = -(c.character (-1) : ℂ) := by
  rw [character_neg_one, character_neg_one]
  by_cases hz : c.parity.val = 0
  · rw [hz, show c'.parity.val = 1 by omega]
    norm_num
  · rw [show c.parity.val = 1 by omega, show c'.parity.val = 0 by omega]
    norm_num

private theorem lo_flip (d : ComplexCharacterData) (s : Fin 2) :
    ((P.lo d (flipParity s)).character (-1) : ℂ) = -((P.lo d s).character (-1) : ℂ) := by
  apply character_neg_of_sum
  change s.val + (s.val + 1) % 2 = 1
  omega

private theorem hi_flip (d : ComplexCharacterData) (s : Fin 2) :
    ((P.hi d (flipParity s)).character (-1) : ℂ) = -((P.hi d s).character (-1) : ℂ) := by
  apply character_neg_of_sum
  change (s.val + d.weight.natAbs + 1) % 2 +
    ((s.val + 1) % 2 + d.weight.natAbs + 1) % 2 = 1
  omega

private theorem left_signs (i : Fin 4) :
    realPositionCharacter (P.X d e sd se) i (-1) =
      if RealCompactParityLifting.inside 0 i then -realPositionCharacter (G.source d e k) i (-1)
      else realPositionCharacter (G.source d e k) i (-1) := by
  fin_cases i
  · change ((P.lo d sd).character (-1) : ℂ) = -((P.lo d (flipParity sd)).character (-1) : ℂ)
    rw [lo_flip, neg_neg]
  · change ((P.hi d sd).character (-1) : ℂ) = -((P.hi d (flipParity sd)).character (-1) : ℂ)
    rw [hi_flip, neg_neg]
  · rfl
  · rfl

private theorem right_signs (i : Fin 4) :
    realPositionCharacter (P.X d e (flipParity sd) (flipParity se)) i (-1) =
      if RealCompactParityLifting.inside 2 i then -realPositionCharacter (G.source d e k) i (-1)
      else realPositionCharacter (G.source d e k) i (-1) := by
  fin_cases i
  · rfl
  · rfl
  · exact lo_flip e se
  · exact hi_flip e se

private theorem middle_halfturn (d e : ComplexCharacterData) (k : ℕ) :
    (-1 : ℂ) ^ (C.cutoff d e k : ℤ) =
      realPositionCharacter (G.source d e k) 1 (-1) * realPositionCharacter (G.source d e k) 2 (-1) := by
  have hpar := pairParity_eq (RealInducedPairPositiveGenericMiddle.rightLower d e k)
    (RealInducedPairPositiveGenericMiddle.leftUpper d)
  rw [zpow_natCast, RealIntegralGenericPolynomial.parity_sign hpar (G.parity_eq d e k),
    neg_one_pow_natAbs hpar]
  exact (G.middleData d e k).par

private theorem all_characters (d e : ComplexCharacterData) (s t : Fin 2) :
    IsCharacterList (P.X d e s t) := by
  intro b hb
  simp only [RealInducedPairQuotientPresentation.X, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩

private theorem inner_low_mem (s t : Fin 2) (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k)
    (hp : Even ((H : ℤ) - 1 - pairParity (P.hi d s) (P.lo e t)))
    (w : KF 4 (P.X d e s t))
    (hw : ∀ j : ℤ, (H : ℤ) ≤ |j| → ∀ x ∈ K₄, Φ 4 1 j w x = 0) :
    w ∈ LinearMap.range (D.innerBinomial d e k s t) := by
  let pre := [RealBlock.character (P.lo d s)]
  let post := [RealBlock.character (P.hi e t)]
  let c := P.hi d s
  let c' := P.lo e t
  have hgap : c'.exponent - c.exponent = (H : ℂ) := D.inner_difference h hH
  let hD := data_D (n := 4) (pre := pre) (post := post) (c := c) (d := c') rfl
    (C.cutoff_pos hH) hp hgap
  let hq := data_q0 (n := 4) (ℓ := H) (pre := pre) (post := post) (c := c) (d := c') rfl
  let hB := data_B (n := 4) (ℓ := H) (pre := pre) (post := post) (c := c) (d := c') rfl
  have hker : w ∈ LinearMap.ker (blockFrobMap hD) :=
    LinearMap.mem_ker.mpr (C.tail_zero_of_low (C.cutoff_pos hH) (pairParity_eq _ _) hp
      (neg_one_pow_sq_fin c'.parity) hD w (fun x hx j hj => hw j hj x hx))
  rw [P.ker_tail_eq_range (C.cutoff_pos hH) (pairParity_eq _ _) hp
    (neg_one_pow_sq_fin c'.parity) hq hB hD] at hker
  exact hker

private theorem left_low_mem (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k)
    (f : KF 4 (G.source d e k))
    (hf : ∀ j : ℤ, (d.weight.natAbs : ℤ) + H ≤ |j| → ∀ x ∈ K₄,
      Φ 4 0 j (G.middle d e k f) x = 0) :
    P.quotientMap d e (flipParity sd) se hd he f ∈
      LinearMap.range (RealInducedPairPositiveCrossedKernel.prefixMap (k := k) hd he) := by
  obtain ⟨w, hw, hmatch⟩ := RealCompactParityLifting.exists_character_lift
    (a := 0) (r := 0) (s := 1) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (N := (d.weight.natAbs : ℤ)) (by exact_mod_cast hd) H (all_characters d e sd se)
    f (G.middle d e k f) left_signs (middle_halfturn d e k)
    (fun j x hx => G.middle_coeff f j hx) (fun j hj x hx => hf j (hj.trans (le_abs_self j)) x hx)
  have heq : P.quotientMap d e sd se hd he w = P.quotientMap d e (flipParity sd) se hd he f := by
    apply (G.quotient_eq_iff hd he w f).mpr
    intro i j hi hj x hx
    simp only [G.pairSign, Ne.symm (G.flipParity_ne_self sd), ↓reduceIte, mul_one]
    have hcoef : ∀ y ∈ K₄, Φ 4 0 i w y = (G.modeSign i • Φ 4 0 i f) y :=
      fun y hy => hmatch i hi y hy
    exact (blockFourierCoefficient_congr_on_compact hcoef hx j).trans
      (blockFourierCoefficient_smul 2 j (G.modeSign i) (Φ 4 0 i f) x)
  obtain ⟨z, hz⟩ := inner_low_mem sd se h hH (C.middle_parity hH) w hw
  exact ⟨z, (congrArg (P.quotientMap d e sd se hd he) hz).trans heq⟩

private theorem right_low_mem (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k)
    (f : KF 4 (G.source d e k))
    (hf : ∀ j : ℤ, (e.weight.natAbs : ℤ) + H ≤ |j| → ∀ x ∈ K₄,
      Φ 4 2 j (G.middle d e k f) x = 0) :
    P.quotientMap d e (flipParity sd) se hd he f ∈ LinearMap.range (F.oppositePrefix (k := k) hd he) := by
  obtain ⟨w, hw, hmatch⟩ := RealCompactParityLifting.exists_character_lift
    (a := 1) (r := 1) (s := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (N := (e.weight.natAbs : ℤ)) (by exact_mod_cast he) H
    (all_characters d e (flipParity sd) (flipParity se))
    f (G.middle d e k f) right_signs (middle_halfturn d e k)
    (fun j x hx => G.middle_coeff f j hx) (fun j hj x hx => hf j (hj.trans (le_abs_self j)) x hx)
  have heq : P.quotientMap d e (flipParity sd) (flipParity se) hd he w =
      P.quotientMap d e (flipParity sd) se hd he f := by
    apply (G.quotient_eq_iff hd he w f).mpr
    intro i j hi hj x hx
    simp only [G.pairSign, G.flipParity_ne_self se, ↓reduceIte, one_mul]
    have hdis : (0 + 1 < (2 : ℕ)) ∨ 2 + 1 < 0 := Or.inl (by decide)
    change Φ 4 2 j (Φ 4 0 i w) x = G.modeSign j * Φ 4 2 j (Φ 4 0 i f) x
    rw [← blockFourierCoefficient_comm hdis (continuous_coe w),
      ← blockFourierCoefficient_comm hdis (continuous_coe f)]
    have hcoef : ∀ y ∈ K₄, Φ 4 2 j w y = (G.modeSign j • Φ 4 2 j f) y :=
      fun y hy => hmatch j hj y hy
    exact (blockFourierCoefficient_congr_on_compact hcoef hx i).trans
      (blockFourierCoefficient_smul 0 i (G.modeSign j) (Φ 4 2 j f) x)
  have hp := D.inner_parity (RealInducedPairPositiveOppositeOuter.opposite_outer_parity hH) hH
  obtain ⟨z, hz⟩ := inner_low_mem (flipParity sd) (flipParity se) h hH hp w hw
  exact ⟨z, (congrArg (P.quotientMap d e (flipParity sd) (flipParity se) hd he) hz).trans heq⟩

/-- The reverse kernel inclusion for the two positive parity prefixes. -/
theorem ker_le_totalPrefix (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k) :
    LinearMap.ker (C.quotient hd he h hH) ≤ F.totalPrefix (k := k) hd he := by
  intro v hv
  obtain ⟨f₀, f₂, hsplit, h₀, h₂⟩ := G.exists_split hd he h hH v (LinearMap.mem_ker.mp hv)
  let q := P.quotientMap d e (flipParity sd) se hd he
  have hsum : q (G.sectionMap hd he k v) = v := P.quotient_section d e _ _ hd he v
  rw [hsplit, map_add] at hsum
  exact Submodule.mem_sup.mpr ⟨q f₀, left_low_mem hd he h hH f₀ h₀,
    q f₂, right_low_mem hd he h hH f₂ h₂, hsum⟩

theorem filtration (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k) :
    RealAdjacentFiltration 4 [] [] (.induced d) (.induced e) :=
  F.filtration hd he h hH ((F.absorption_iff_ker_le hd he h hH).mpr (ker_le_totalPrefix hd he h hH))

end Langlands.Archimedean.RealInducedPairPositiveFiltration

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean RealInducedPairLinkedReplacement

/-- The adjacent filtration in the linked region with positive weights and
positive signed inner weight. -/
def RealInducedPairPositiveFiltrationStatement : Prop :=
  ∀ (d e : ComplexCharacterData) (k : ℕ),
    0 < d.weight.natAbs → 0 < e.weight.natAbs →
    IsLinkedAt d e k → 0 < innerWeight d e k →
    RealAdjacentFiltration 4 [] [] (.induced d) (.induced e)

theorem realInducedPairPositiveFiltration : RealInducedPairPositiveFiltrationStatement :=
  fun _ _ _ => RealInducedPairPositiveFiltration.filtration

end Langlands.Archimedean

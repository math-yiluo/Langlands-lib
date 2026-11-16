import Langlands.Representation.Archimedean.RealBlockMultiplierSlices
import Langlands.Representation.Archimedean.RealCharacterInducedGeneric
import Langlands.Representation.Archimedean.RealInjectiveIntertwinerStages

/-!
# The generic four-character construction for two induction blocks

The four crossing multipliers are generic. Two paths differing by disjoint
middle crossings preserve the two target induction windows.
-/

noncomputable section

open scoped TensorProduct Matrix Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean
namespace RealInducedSwapGeneric

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open RealBlockFrobeniusMap RealBlockPosition RealBlockMultiplier RealCharacterPair
open RealCharacterPairReducible RealBlockJacquet RealStandardFiltration
open RealCharacterInducedSwap RealCharacterInducedPushforward
open InductionStages RealBlockMultiplierSlices RealDisjointBlockMultipliers

attribute [local instance 100] LieRing.ofAssociativeRing

variable (d e : ComplexCharacterData)

/-- Expand both induction blocks into their four position characters. -/
def expanded : List RealBlock :=
  [.character (chA d), .character (chB d), .character (chA e), .character (chB e)]

abbrev source : List RealBlock := [.induced d, .induced e]
abbrev target : List RealBlock := [.induced e, .induced d]
abbrev crossed : List RealBlock :=
  [.character (chA d), .character (chA e), .character (chB d), .character (chB e)]
abbrev movedLeft : List RealBlock :=
  [.character (chA e), .character (chA d), .character (chB d), .character (chB e)]
abbrev movedRight : List RealBlock :=
  [.character (chA d), .character (chA e), .character (chB e), .character (chB d)]
abbrev middle : List RealBlock :=
  [.character (chA e), .character (chA d), .character (chB e), .character (chB d)]

abbrev keepFirst : List RealBlock := [.induced d, .character (chA e), .character (chB e)]
abbrev keepSecond : List RealBlock := [.character (chA d), .character (chB d), .induced e]
abbrev firstMoved : List RealBlock := [.character (chA e), .induced d, .character (chB e)]
abbrev secondMoved : List RealBlock := [.character (chA d), .induced e, .character (chB d)]

theorem pairParity_comm (x y : RealCharacterData) : pairParity x y = pairParity y x := by
  simp only [pairParity, Nat.add_comm]

/-- The multiplier for swapping adjacent source characters `x,y`. -/
def multiplier (x y : RealCharacterData) : ℤ → ℂ :=
  genericMultiplier (x.exponent - y.exponent) (pairParity y x)

/-- All four crossings avoid both rank-one exceptional sets. -/
def IsGenericPair : Prop :=
  IsGenericParameter ((chB d).exponent - (chA e).exponent) (pairParity (chA e) (chB d)) ∧
  IsGenericParameter ((chA d).exponent - (chA e).exponent) (pairParity (chA e) (chA d)) ∧
  IsGenericParameter ((chB d).exponent - (chB e).exponent) (pairParity (chB e) (chB d)) ∧
  IsGenericParameter ((chA d).exponent - (chB e).exponent) (pairParity (chB e) (chA d))

theorem pos_expanded : realPositionCharacter (expanded d e) = realPositionCharacter (source d e) := by
  funext i x
  rw [realPositionCharacter_eq_charFun, realPositionCharacter_eq_charFun]
  rcases i with _ | _ | _ | _ | i <;> rfl

theorem pos_keepFirst : realPositionCharacter (keepFirst d e) = realPositionCharacter (source d e) := by
  funext i x
  rw [realPositionCharacter_eq_charFun, realPositionCharacter_eq_charFun]
  rcases i with _ | _ | _ | _ | i <;> rfl

theorem pos_keepSecond : realPositionCharacter (keepSecond d e) = realPositionCharacter (source d e) := by
  funext i x
  rw [realPositionCharacter_eq_charFun, realPositionCharacter_eq_charFun]
  rcases i with _ | _ | _ | _ | i <;> rfl

theorem pos_firstMoved : realPositionCharacter (firstMoved d e) = realPositionCharacter (movedLeft d e) := by
  funext i x
  rw [realPositionCharacter_eq_charFun, realPositionCharacter_eq_charFun]
  rcases i with _ | _ | _ | _ | i <;> rfl

theorem pos_secondMoved : realPositionCharacter (secondMoved d e) = realPositionCharacter (movedRight d e) := by
  funext i x
  rw [realPositionCharacter_eq_charFun, realPositionCharacter_eq_charFun]
  rcases i with _ | _ | _ | _ | i <;> rfl

theorem no_induced_expanded (p : ℕ) : realInducedBlockAt (expanded d e) p = none := by
  rcases p with _ | _ | _ | _ | p <;> rfl

theorem no_induced_movedLeft (p : ℕ) : realInducedBlockAt (movedLeft d e) p = none := by
  rcases p with _ | _ | _ | _ | p <;> rfl

theorem no_induced_movedRight (p : ℕ) : realInducedBlockAt (movedRight d e) p = none := by
  rcases p with _ | _ | _ | _ | p <;> rfl

theorem kFin_le_of_conditions {n : ℕ} {xs ys : List RealBlock}
    (hpos : realPositionCharacter ys = realPositionCharacter xs)
    (hind : ∀ p z, realInducedBlockAt ys p = some z → realInducedBlockAt xs p = some z) :
    KF n xs ≤ KF n ys := by
  intro f hf
  refine ⟨?_, hf.2⟩
  apply (mem_realStandardModule_iff n ys f).mpr
  refine ⟨?_, fun p z hz j hj g => hf.1.2 p z (hind p z hz) j hj g⟩
  rw [hpos]
  exact hf.1.1

theorem source_le_expanded : KF 4 (source d e) ≤ KF 4 (expanded d e) :=
  kFin_le_of_conditions (pos_expanded d e) fun p z hz => by
    rw [no_induced_expanded] at hz
    contradiction

theorem source_le_keepFirst : KF 4 (source d e) ≤ KF 4 (keepFirst d e) := by
  apply kFin_le_of_conditions (pos_keepFirst d e)
  intro p z hz
  rcases p with _ | _ | _ | _ | p
  · simpa only [keepFirst, source, realInducedBlockAt] using hz
  all_goals simp [realInducedBlockAt] at hz

theorem source_le_keepSecond : KF 4 (source d e) ≤ KF 4 (keepSecond d e) := by
  apply kFin_le_of_conditions (pos_keepSecond d e)
  intro p z hz
  rcases p with _ | _ | _ | _ | p
  · simp [realInducedBlockAt] at hz
  · simp [realInducedBlockAt] at hz
  · simpa only [keepSecond, source, realInducedBlockAt] using hz
  all_goals simp [realInducedBlockAt] at hz

theorem mem_firstMoved (f : KF 4 (movedLeft d e))
    (hw : ∀ g ∈ unitaryCompact ℝ 4, ∀ j : ℤ, |j| < (d.weight.natAbs : ℤ) →
      blockFourierCoefficient 4 1 j (f : Langlands.GeneralLinear 4 ℝ → ℂ) g = 0) :
    (f : Langlands.GeneralLinear 4 ℝ → ℂ) ∈ KF 4 (firstMoved d e) := by
  refine ⟨RealBlockPosition.mem_realStandardModule_of_unitaryCompact
    (N := 4) (ds := firstMoved d e) rfl ?_ ?_, f.2.2⟩
  · rw [pos_firstMoved]
    exact f.2.1.1
  · intro p z hz j hj g hg
    rcases p with _ | _ | _ | _ | p
    · simp [realInducedBlockAt] at hz
    · simp only [realInducedBlockAt, Option.some.injEq] at hz
      subst z
      exact hw g hg j (by simpa only [Int.abs_eq_natAbs] using hj)
    all_goals simp [realInducedBlockAt] at hz

theorem mem_secondMoved (f : KF 4 (movedRight d e))
    (hw : ∀ g ∈ unitaryCompact ℝ 4, ∀ j : ℤ, |j| < (e.weight.natAbs : ℤ) →
      blockFourierCoefficient 4 1 j (f : Langlands.GeneralLinear 4 ℝ → ℂ) g = 0) :
    (f : Langlands.GeneralLinear 4 ℝ → ℂ) ∈ KF 4 (secondMoved d e) := by
  refine ⟨RealBlockPosition.mem_realStandardModule_of_unitaryCompact
    (N := 4) (ds := secondMoved d e) rfl ?_ ?_, f.2.2⟩
  · rw [pos_secondMoved]
    exact f.2.1.1
  · intro p z hz j hj g hg
    rcases p with _ | _ | _ | _ | p
    · simp [realInducedBlockAt] at hz
    · simp only [realInducedBlockAt, Option.some.injEq] at hz
      subst z
      exact hw g hg j (by simpa only [Int.abs_eq_natAbs] using hj)
    all_goals simp [realInducedBlockAt] at hz

section Swap

variable {n : ℕ} (pre post : List RealBlock) (x y : RealCharacterData)

/-- Frobenius data for a generic character crossing in any context. -/
theorem swapData
    (hr : realRank (pre ++ .character x :: .character y :: post) = n) :
    IsBlockFrobData n (pre ++ .character x :: .character y :: post)
      (pre ++ .character y :: .character x :: post) (realRank pre)
      (pairParity y x) (sigma0 y x) (multiplier x y) := by
  simpa only [dc, mid_pair, multiplier] using
    (data_swap (c := y) (d := x)
      (by simpa only [mid_pair] using realRank_dc_mid hr)
      (isSymmetric_genericMultiplier (x.exponent - y.exponent) (pairParity_eq y x)))

theorem swap_injective
    (hr : realRank (pre ++ .character x :: .character y :: post) = n)
    (hgen : IsGenericParameter (x.exponent - y.exponent) (pairParity y x)) :
    Function.Injective (blockFrobMap (swapData pre post x y hr)) :=
  frob_injective_of_ne_zero _ fun j _ => genericMultiplier_ne_zero_of_ne hgen.1 hgen.2 j

theorem swap_modulo
    (hr : realRank (pre ++ .character x :: .character y :: post) = n)
    (hgen : IsGenericParameter (x.exponent - y.exponent) (pairParity y x)) :
    IsRealIntertwinerModulo n (pre ++ .character x :: .character y :: post)
      (pre ++ .character y :: .character x :: post) ⊥
      (blockFrobMap (swapData pre post x y hr)) := by
  refine isRealIntertwinerModulo_blockFrobMap _ ?_ ⊥
  have h0 : GramFormula.realPositionExponent
      (pre ++ .character x :: .character y :: post) (realRank pre) = x.exponent := by
    simpa only [mid_pair, GramFormula.realPositionExponent] using
      (exponent_mid_zero pre post (ws := [.character x, .character y]) (by change 0 < 2; decide))
  have h1 : GramFormula.realPositionExponent
      (pre ++ .character x :: .character y :: post) (realRank pre + 1) = y.exponent := by
    simpa only [mid_pair, GramFormula.realPositionExponent] using
      (exponent_mid_one pre post (ws := [.character x, .character y]) (by change 1 < 2; decide))
  rw [h0, h1]
  exact isRecurrent_genericMultiplier_of_ne (pairParity_eq y x) hgen.2

end Swap

section Landing

variable (c : RealCharacterData) (z : ComplexCharacterData)

/-- The proved induced-first landing with the two chosen generic multipliers. -/
theorem inducedFirst_landing
    (hB : IsGenericParameter ((chB z).exponent - c.exponent) (pairParity c (chB z)))
    (hA : IsGenericParameter ((chA z).exponent - c.exponent) (pairParity c (chA z)))
    (f H U : Langlands.GeneralLinear 3 ℝ → ℂ)
    (hf : f ∈ KFin 3 (lDC c z)) (hH : Continuous H) (hU : Continuous U)
    (hμ : ∀ g ∈ unitaryCompact ℝ 3, ∀ j : ℤ,
      blockFourierCoefficient 3 1 j H g =
        multiplier (chB z) c j * blockFourierCoefficient 3 1 j f g)
    (hν : ∀ g ∈ unitaryCompact ℝ 3, ∀ j : ℤ,
      blockFourierCoefficient 3 0 j U g =
        multiplier (chA z) c j * blockFourierCoefficient 3 0 j H g) :
    ∀ g ∈ unitaryCompact ℝ 3, ∀ j : ℤ, |j| < (z.weight.natAbs : ℤ) →
      blockFourierCoefficient 3 1 j U g = 0 := by
  have hparB := even_class_chB_c c z
  have hsignB := sign_class_chB_c c z
  rw [pairParity_comm (chB z) c] at hparB hsignB
  have hrecB := isRecurrent_genericMultiplier_of_ne (pairParity_eq c (chB z)) hB.2
  have hrecA := isRecurrent_genericMultiplier_of_ne (pairParity_eq c (chA z)) hA.2
  have hparam : (chB z).exponent - c.exponent + 1 + (z.weight.natAbs : ℂ) =
      (chA z).exponent - c.exponent + 1 := by
    rw [chA_exponent, chB_exponent]
    ring
  have hrecA' : IsRecurrent
      ((chB z).exponent - c.exponent + 1 + (z.weight.natAbs : ℂ))
      ((z.weight.natAbs + 1 + c.parity.val : ℕ) : ℤ) (multiplier (chA z) c) := by
    rw [hparam]
    exact isRecurrent_of_even hrecA (even_class_c_chA c z)
  have hland := RealSwapLandingIntegral.inducedFirst c z
    ((chB z).exponent - c.exponent + 1) (multiplier (chA z) c) (multiplier (chB z) c)
    f H U (isRecurrent_of_even hrecB hparB)
    (isSymmetric_of_even (isSymmetric_genericMultiplier _ (pairParity_eq c (chB z)))
      hparB hsignB)
    hrecA'
    (isSymmetric_of_even (isSymmetric_genericMultiplier _ (pairParity_eq c (chA z)))
      (even_class_c_chA c z) (sign_class_c_chA c z))
    hf hH hU hμ hν
  simpa only [Int.abs_eq_natAbs] using hland

/-- The proved character-first landing with the two chosen generic multipliers. -/
theorem characterFirst_landing
    (hA : IsGenericParameter (c.exponent - (chA z).exponent) (pairParity (chA z) c))
    (hB : IsGenericParameter (c.exponent - (chB z).exponent) (pairParity (chB z) c))
    (f H U : Langlands.GeneralLinear 3 ℝ → ℂ)
    (hf : f ∈ KFin 3 (lCD c z)) (hH : Continuous H) (hU : Continuous U)
    (hμ : ∀ g ∈ unitaryCompact ℝ 3, ∀ j : ℤ,
      blockFourierCoefficient 3 0 j H g =
        multiplier c (chA z) j * blockFourierCoefficient 3 0 j f g)
    (hν : ∀ g ∈ unitaryCompact ℝ 3, ∀ j : ℤ,
      blockFourierCoefficient 3 1 j U g =
        multiplier c (chB z) j * blockFourierCoefficient 3 1 j H g) :
    ∀ g ∈ unitaryCompact ℝ 3, ∀ j : ℤ, |j| < (z.weight.natAbs : ℤ) →
      blockFourierCoefficient 3 0 j U g = 0 := by
  have hparA := even_class_c_chA c z
  have hsignA := sign_class_c_chA c z
  rw [pairParity_comm c (chA z)] at hparA hsignA
  have hrecA := isRecurrent_genericMultiplier_of_ne (pairParity_eq (chA z) c) hA.2
  have hrecB := isRecurrent_genericMultiplier_of_ne (pairParity_eq (chB z) c) hB.2
  have hparam : c.exponent - (chA z).exponent + 1 + (z.weight.natAbs : ℂ) =
      c.exponent - (chB z).exponent + 1 := by
    rw [chA_exponent, chB_exponent]
    ring
  have hrecB' : IsRecurrent
      (c.exponent - (chA z).exponent + 1 + (z.weight.natAbs : ℂ))
      (c.parity.val : ℤ) (multiplier c (chB z)) := by
    rw [hparam]
    exact isRecurrent_of_even hrecB (even_class_chB_c c z)
  have hland := (RealSwapLandingMirror.characterFirst_of_inducedFirst
    RealSwapLandingIntegral.inducedFirst) c z
    (c.exponent - (chA z).exponent + 1) (multiplier c (chA z)) (multiplier c (chB z))
    f H U (isRecurrent_of_even hrecA hparA)
    (isSymmetric_of_even (isSymmetric_genericMultiplier _ (pairParity_eq (chA z) c))
      hparA hsignA)
    hrecB'
    (isSymmetric_of_even (isSymmetric_genericMultiplier _ (pairParity_eq (chB z) c))
      (even_class_chB_c c z) (sign_class_chB_c c z))
    hf hH hU hμ hν
  simpa only [Int.abs_eq_natAbs] using hland

end Landing

/-! ## The six character crossings and their disjoint square -/

theorem dataBC : IsBlockFrobData 4 (expanded d e) (crossed d e) 1
    (pairParity (chA e) (chB d)) (sigma0 (chA e) (chB d))
    (multiplier (chB d) (chA e)) :=
  swapData [.character (chA d)] [.character (chB e)] (chB d) (chA e) rfl

theorem dataAC : IsBlockFrobData 4 (crossed d e) (movedLeft d e) 0
    (pairParity (chA e) (chA d)) (sigma0 (chA e) (chA d))
    (multiplier (chA d) (chA e)) :=
  swapData [] [.character (chB d), .character (chB e)] (chA d) (chA e) rfl

theorem dataBD : IsBlockFrobData 4 (movedLeft d e) (middle d e) 2
    (pairParity (chB e) (chB d)) (sigma0 (chB e) (chB d))
    (multiplier (chB d) (chB e)) :=
  swapData [.character (chA e), .character (chA d)] [] (chB d) (chB e) rfl

theorem dataBD' : IsBlockFrobData 4 (crossed d e) (movedRight d e) 2
    (pairParity (chB e) (chB d)) (sigma0 (chB e) (chB d))
    (multiplier (chB d) (chB e)) :=
  swapData [.character (chA d), .character (chA e)] [] (chB d) (chB e) rfl

theorem dataAC' : IsBlockFrobData 4 (movedRight d e) (middle d e) 0
    (pairParity (chA e) (chA d)) (sigma0 (chA e) (chA d))
    (multiplier (chA d) (chA e)) :=
  swapData [] [.character (chB e), .character (chB d)] (chA d) (chA e) rfl

theorem dataAD : IsBlockFrobData 4 (middle d e) (expanded e d) 1
    (pairParity (chB e) (chA d)) (sigma0 (chB e) (chA d))
    (multiplier (chA d) (chB e)) :=
  swapData [.character (chA e)] [.character (chB d)] (chA d) (chB e) rfl

/-- The two middle crossings act on disjoint coordinate pairs. -/
theorem middle_square (f : KF 4 (crossed d e)) :
    blockFrobMap (dataBD d e) (blockFrobMap (dataAC d e) f) =
      blockFrobMap (dataAC' d e) (blockFrobMap (dataBD' d e) f) :=
  blockFrobMap_commuting_square (Or.inl (by decide))
    (dataAC d e) (dataBD' d e) (dataBD d e) (dataAC' d e) f

/-- Forget the two original Fourier conditions and apply the four crossings. -/
def rawMap : KF 4 (source d e) →ₗ[ℂ] KF 4 (expanded e d) :=
  blockFrobMap (dataAD d e) ∘ₗ blockFrobMap (dataBD d e) ∘ₗ
    blockFrobMap (dataAC d e) ∘ₗ blockFrobMap (dataBC d e) ∘ₗ
      Submodule.inclusion (source_le_expanded d e)

/-- The first pair of crossings transports the first induction window once. -/
theorem first_window_once (hgen : IsGenericPair d e) (f : KF 4 (source d e)) :
    ∀ g ∈ unitaryCompact ℝ 4, ∀ j : ℤ, |j| < (d.weight.natAbs : ℤ) →
      blockFourierCoefficient 4 1 j
        (blockFrobMap (dataAC d e)
          (blockFrobMap (dataBC d e) (Submodule.inclusion (source_le_expanded d e) f)) :
            Langlands.GeneralLinear 4 ℝ → ℂ) g = 0 := by
  let f0 : KF 4 (expanded d e) := Submodule.inclusion (source_le_expanded d e) f
  let H : KF 4 (crossed d e) := blockFrobMap (dataBC d e) f0
  let U : KF 4 (movedLeft d e) := blockFrobMap (dataAC d e) H
  let f' : KFin 4 ([] ++ lDC (chA e) d ++ [.character (chB e)]) :=
    ⟨(f : Langlands.GeneralLinear 4 ℝ → ℂ), source_le_keepFirst d e f.2⟩
  exact twoStep_landing_in_stages (n := 4) (a := 0) (r := 3)
    (pre := []) (ds := lDC (chA e) d) (post := [.character (chB e)])
    (by decide) rfl rfl (p := 1) (q := 0) (t := 1) (L := d.weight.natAbs)
    (by decide) (by decide) (by decide)
    (multiplier (chB d) (chA e)) (multiplier (chA d) (chA e))
    (inducedFirst_landing (chA e) d hgen.1 hgen.2.1) f'
    H.2.1.1.1 U.2.1.1.1
    (fun g hg j => blockFourierCoefficient_blockFrobMap (dataBC d e) f0 hg j)
    (fun g hg j => blockFourierCoefficient_blockFrobMap (dataAC d e) H hg j)

/-- Both induced-first landings put the first induction window in its final position. -/
theorem first_window (hgen : IsGenericPair d e) (f : KF 4 (source d e)) :
    ∀ g ∈ unitaryCompact ℝ 4, ∀ j : ℤ, |j| < (d.weight.natAbs : ℤ) →
      blockFourierCoefficient 4 2 j
        (rawMap d e f : Langlands.GeneralLinear 4 ℝ → ℂ) g = 0 := by
  let f0 : KF 4 (expanded d e) := Submodule.inclusion (source_le_expanded d e) f
  let f1 : KF 4 (crossed d e) := blockFrobMap (dataBC d e) f0
  let f2 : KF 4 (movedLeft d e) := blockFrobMap (dataAC d e) f1
  let H : KF 4 (middle d e) := blockFrobMap (dataBD d e) f2
  let U : KF 4 (expanded e d) := blockFrobMap (dataAD d e) H
  let f' : KFin 4 ([.character (chA e)] ++ lDC (chB e) d ++ []) :=
    ⟨(f2 : Langlands.GeneralLinear 4 ℝ → ℂ),
      mem_firstMoved d e f2 (first_window_once d e hgen f)⟩
  exact twoStep_landing_in_stages (n := 4) (a := 1) (r := 3)
    (pre := [.character (chA e)]) (ds := lDC (chB e) d) (post := [])
    (by decide) rfl rfl (p := 1) (q := 0) (t := 1) (L := d.weight.natAbs)
    (by decide) (by decide) (by decide)
    (multiplier (chB d) (chB e)) (multiplier (chA d) (chB e))
    (inducedFirst_landing (chB e) d hgen.2.2.1 hgen.2.2.2) f'
    H.2.1.1.1 U.2.1.1.1
    (fun g hg j => blockFourierCoefficient_blockFrobMap (dataBD d e) f2 hg j)
    (fun g hg j => blockFourierCoefficient_blockFrobMap (dataAD d e) H hg j)

/-- On the other path, the first pair of crossings transports the second window once. -/
theorem second_window_once (hgen : IsGenericPair d e) (f : KF 4 (source d e)) :
    ∀ g ∈ unitaryCompact ℝ 4, ∀ j : ℤ, |j| < (e.weight.natAbs : ℤ) →
      blockFourierCoefficient 4 1 j
        (blockFrobMap (dataBD' d e)
          (blockFrobMap (dataBC d e) (Submodule.inclusion (source_le_expanded d e) f)) :
            Langlands.GeneralLinear 4 ℝ → ℂ) g = 0 := by
  let f0 : KF 4 (expanded d e) := Submodule.inclusion (source_le_expanded d e) f
  let H : KF 4 (crossed d e) := blockFrobMap (dataBC d e) f0
  let U : KF 4 (movedRight d e) := blockFrobMap (dataBD' d e) H
  let f' : KFin 4 ([.character (chA d)] ++ lCD (chB d) e ++ []) :=
    ⟨(f : Langlands.GeneralLinear 4 ℝ → ℂ), source_le_keepSecond d e f.2⟩
  exact twoStep_landing_in_stages (n := 4) (a := 1) (r := 3)
    (pre := [.character (chA d)]) (ds := lCD (chB d) e) (post := [])
    (by decide) rfl rfl (p := 0) (q := 1) (t := 0) (L := e.weight.natAbs)
    (by decide) (by decide) (by decide)
    (multiplier (chB d) (chA e)) (multiplier (chB d) (chB e))
    (characterFirst_landing (chB d) e hgen.1 hgen.2.2.1) f'
    H.2.1.1.1 U.2.1.1.1
    (fun g hg j => blockFourierCoefficient_blockFrobMap (dataBC d e) f0 hg j)
    (fun g hg j => blockFourierCoefficient_blockFrobMap (dataBD' d e) H hg j)

/-- The disjoint square identifies the second-window path with the chosen map. -/
theorem second_window (hgen : IsGenericPair d e) (f : KF 4 (source d e)) :
    ∀ g ∈ unitaryCompact ℝ 4, ∀ j : ℤ, |j| < (e.weight.natAbs : ℤ) →
      blockFourierCoefficient 4 0 j
        (rawMap d e f : Langlands.GeneralLinear 4 ℝ → ℂ) g = 0 := by
  let f0 : KF 4 (expanded d e) := Submodule.inclusion (source_le_expanded d e) f
  let f1 : KF 4 (crossed d e) := blockFrobMap (dataBC d e) f0
  let f2 : KF 4 (movedRight d e) := blockFrobMap (dataBD' d e) f1
  let H : KF 4 (middle d e) := blockFrobMap (dataAC' d e) f2
  let U : KF 4 (expanded e d) := blockFrobMap (dataAD d e) H
  let f' : KFin 4 ([] ++ lCD (chA d) e ++ [.character (chB d)]) :=
    ⟨(f2 : Langlands.GeneralLinear 4 ℝ → ℂ),
      mem_secondMoved d e f2 (second_window_once d e hgen f)⟩
  have hland := twoStep_landing_in_stages (n := 4) (a := 0) (r := 3)
    (pre := []) (ds := lCD (chA d) e) (post := [.character (chB d)])
    (by decide) rfl rfl (p := 0) (q := 1) (t := 0) (L := e.weight.natAbs)
    (by decide) (by decide) (by decide)
    (multiplier (chA d) (chA e)) (multiplier (chA d) (chB e))
    (characterFirst_landing (chA d) e hgen.2.1 hgen.2.2.2) f'
    H.2.1.1.1 U.2.1.1.1
    (fun g hg j => blockFourierCoefficient_blockFrobMap (dataAC' d e) f2 hg j)
    (fun g hg j => blockFourierCoefficient_blockFrobMap (dataAD d e) H hg j)
  have heq : rawMap d e f = U := by
    change blockFrobMap (dataAD d e)
      (blockFrobMap (dataBD d e) (blockFrobMap (dataAC d e) f1)) =
        blockFrobMap (dataAD d e)
          (blockFrobMap (dataAC' d e) (blockFrobMap (dataBD' d e) f1))
    rw [middle_square]
  rw [heq]
  exact hland

/-- Compact vanishing for both windows gives membership in the actual target module. -/
theorem rawMap_mem_target (hgen : IsGenericPair d e) (f : KF 4 (source d e)) :
    (rawMap d e f : Langlands.GeneralLinear 4 ℝ → ℂ) ∈ KF 4 (target d e) := by
  refine ⟨RealBlockPosition.mem_realStandardModule_of_unitaryCompact
    (N := 4) (ds := target d e) rfl ?_ ?_, (rawMap d e f).2.2⟩
  · rw [← pos_expanded e d]
    exact (rawMap d e f).2.1.1
  · intro p z hz j hj g hg
    rcases p with _ | _ | _ | _ | p
    · simp only [realInducedBlockAt, Option.some.injEq] at hz
      subst z
      exact second_window d e hgen f g hg j (by simpa only [Int.abs_eq_natAbs] using hj)
    · simp [realInducedBlockAt] at hz
    · simp only [realInducedBlockAt, Option.some.injEq] at hz
      subst z
      exact first_window d e hgen f g hg j (by simpa only [Int.abs_eq_natAbs] using hj)
    all_goals simp [realInducedBlockAt] at hz

/-- Each generic factor intertwines exactly, as does the source inclusion. -/
theorem rawMap_modulo (hgen : IsGenericPair d e) :
    IsRealIntertwinerModulo 4 (source d e) (expanded e d) ⊥ (rawMap d e) := by
  have hinc : IsRealIntertwinerModulo 4 (source d e) (expanded d e) ⊥
      (Submodule.inclusion (source_le_expanded d e)) :=
    modulo_bot_of_coe (modulo_id (source d e)) (fun _ => rfl)
  exact modulo_comp_bot
    (swap_modulo [.character (chA e)] [.character (chB d)]
      (chA d) (chB e) rfl hgen.2.2.2)
    (modulo_comp_bot
      (swap_modulo [.character (chA e), .character (chA d)] []
        (chB d) (chB e) rfl hgen.2.2.1)
      (modulo_comp_bot
        (swap_modulo [] [.character (chB d), .character (chB e)]
          (chA d) (chA e) rfl hgen.2.1)
        (modulo_comp_bot
          (swap_modulo [.character (chA d)] [.character (chB e)]
            (chB d) (chA e) rfl hgen.1) hinc)))

/-- No factor of the generic composite has a kernel. -/
theorem rawMap_injective (hgen : IsGenericPair d e) : Function.Injective (rawMap d e) :=
  (swap_injective [.character (chA e)] [.character (chB d)]
    (chA d) (chB e) rfl hgen.2.2.2).comp
  ((swap_injective [.character (chA e), .character (chA d)] []
    (chB d) (chB e) rfl hgen.2.2.1).comp
  ((swap_injective [] [.character (chB d), .character (chB e)]
    (chA d) (chA e) rfl hgen.2.1).comp
  ((swap_injective [.character (chA d)] [.character (chB e)]
    (chB d) (chA e) rfl hgen.1).comp
    (Submodule.inclusion_injective (source_le_expanded d e)))))

/-- The generic four-character composite as a map between the two actual standard modules. -/
def genericMap (hgen : IsGenericPair d e) : KF 4 (source d e) →ₗ[ℂ] KF 4 (target d e) :=
  LinearMap.codRestrict (KF 4 (target d e))
    ((KF 4 (expanded e d)).subtype ∘ₗ rawMap d e) (rawMap_mem_target d e hgen)

/-- Swapping two induction blocks when all four constituent crossings are generic. -/
theorem injective_of_generic (hgen : IsGenericPair d e) :
    RealInjectiveIntertwinerExists 4 (source d e) (target d e) := by
  have hm : IsRealIntertwinerModulo 4 (source d e) (target d e) ⊥ (genericMap d e hgen) :=
    modulo_bot_of_coe (rawMap_modulo d e hgen) (fun _ => rfl)
  have hi : Function.Injective (genericMap d e hgen) := by
    intro f g hfg
    apply rawMap_injective d e hgen
    apply Subtype.ext
    exact congrArg (fun v : KF 4 (target d e) =>
      (v : Langlands.GeneralLinear 4 ℝ → ℂ)) hfg
  refine ⟨genericMap d e hgen, hi, ?_⟩
  simpa only [LinearMap.id_comp] using
    hm.comp (isRealStandardIntertwiner_id 4 (target d e)) bot_le

/-- The generic swap extends through arbitrary surrounding induction blocks. -/
theorem injective_in_stages {n : ℕ} (pre post : List RealBlock)
    (hr : realRank (pre ++ .induced d :: .induced e :: post) = n)
    (hgen : IsGenericPair d e) :
    RealInjectiveIntertwinerExists n (pre ++ .induced d :: .induced e :: post)
      (pre ++ .induced e :: .induced d :: post) := by
  simpa only [source, target, mid_pair] using
    (injective_of_generic d e hgen).in_stages pre post rfl rfl
      (by simpa only [source, mid_pair] using hr)

end RealInducedSwapGeneric
end Langlands.Archimedean

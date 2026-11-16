import Langlands.Representation.Archimedean.RealInducedSwapGeneric

/-!
# Recurrent four-crossing maps and finite-support cancellation

The four crossing sequences need only satisfy recurrence and reflection symmetry.
The two target induction windows persist, although injectivity need not hold.
-/

noncomputable section

open scoped TensorProduct Matrix Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean
namespace RealInducedSwapRecurrent

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open RealBlockFrobeniusMap RealBlockPosition RealBlockMultiplier RealCharacterPair
open RealCharacterPairReducible RealBlockJacquet RealStandardFiltration
open RealCharacterInducedSwap RealCharacterInducedPushforward
open InductionStages RealBlockMultiplierSlices RealDisjointBlockMultipliers
open RealInducedSwapGeneric

attribute [local instance 100] LieRing.ofAssociativeRing

/-- A recurrent symmetric sequence for crossing the adjacent source characters `x,y`. -/
structure Crossing (x y : RealCharacterData) where
  μ : ℤ → ℂ
  symm : IsSymmetric (pairParity y x) (sigma0 y x) μ
  recurrent : IsRecurrent (x.exponent - y.exponent + 1) (pairParity y x) μ

/-- The four independent recurrent crossing sequences. -/
structure FourCrossings (d e : ComplexCharacterData) where
  bc : Crossing (chB d) (chA e)
  ac : Crossing (chA d) (chA e)
  bd : Crossing (chB d) (chB e)
  ad : Crossing (chA d) (chB e)

section Swap

variable {n : ℕ} (pre post : List RealBlock) (x y : RealCharacterData) (h : Crossing x y)

/-- Frobenius data for a symmetric crossing in an arbitrary context. -/
theorem swapData
    (hr : realRank (pre ++ .character x :: .character y :: post) = n) :
    IsBlockFrobData n (pre ++ .character x :: .character y :: post)
      (pre ++ .character y :: .character x :: post) (realRank pre)
      (pairParity y x) (sigma0 y x) h.μ := by
  simpa only [dc, mid_pair] using
    (data_swap (c := y) (d := x)
      (by simpa only [mid_pair] using realRank_dc_mid hr) h.symm)

/-- The recurrence makes the crossing an exact intertwiner. -/
theorem swap_modulo
    (hr : realRank (pre ++ .character x :: .character y :: post) = n) :
    IsRealIntertwinerModulo n (pre ++ .character x :: .character y :: post)
      (pre ++ .character y :: .character x :: post) ⊥
      (blockFrobMap (swapData pre post x y h hr)) := by
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
  exact h.recurrent

end Swap

section Landing

variable (c : RealCharacterData) (z : ComplexCharacterData)

/-- The induced-first landing for two arbitrary recurrent crossings. -/
theorem inducedFirst_landing
    (hB : Crossing (chB z) c)
    (hA : Crossing (chA z) c)
    (f H U : Langlands.GeneralLinear 3 ℝ → ℂ)
    (hf : f ∈ KFin 3 (lDC c z)) (hH : Continuous H) (hU : Continuous U)
    (hμ : ∀ g ∈ unitaryCompact ℝ 3, ∀ j : ℤ,
      blockFourierCoefficient 3 1 j H g =
        hB.μ j * blockFourierCoefficient 3 1 j f g)
    (hν : ∀ g ∈ unitaryCompact ℝ 3, ∀ j : ℤ,
      blockFourierCoefficient 3 0 j U g =
        hA.μ j * blockFourierCoefficient 3 0 j H g) :
    ∀ g ∈ unitaryCompact ℝ 3, ∀ j : ℤ, |j| < (z.weight.natAbs : ℤ) →
      blockFourierCoefficient 3 1 j U g = 0 := by
  have hparB := even_class_chB_c c z
  have hsignB := sign_class_chB_c c z
  rw [pairParity_comm (chB z) c] at hparB hsignB
  have hrecB := hB.recurrent
  have hrecA := hA.recurrent
  have hparam : (chB z).exponent - c.exponent + 1 + (z.weight.natAbs : ℂ) =
      (chA z).exponent - c.exponent + 1 := by
    rw [chA_exponent, chB_exponent]
    ring
  have hrecA' : IsRecurrent
      ((chB z).exponent - c.exponent + 1 + (z.weight.natAbs : ℂ))
      ((z.weight.natAbs + 1 + c.parity.val : ℕ) : ℤ) (hA.μ) := by
    rw [hparam]
    exact isRecurrent_of_even hrecA (even_class_c_chA c z)
  have hland := RealSwapLandingIntegral.inducedFirst c z
    ((chB z).exponent - c.exponent + 1) (hA.μ) (hB.μ)
    f H U (isRecurrent_of_even hrecB hparB)
    (isSymmetric_of_even hB.symm
      hparB hsignB)
    hrecA'
    (isSymmetric_of_even hA.symm
      (even_class_c_chA c z) (sign_class_c_chA c z))
    hf hH hU hμ hν
  simpa only [Int.abs_eq_natAbs] using hland

/-- The character-first landing for two arbitrary recurrent crossings. -/
theorem characterFirst_landing
    (hA : Crossing c (chA z))
    (hB : Crossing c (chB z))
    (f H U : Langlands.GeneralLinear 3 ℝ → ℂ)
    (hf : f ∈ KFin 3 (lCD c z)) (hH : Continuous H) (hU : Continuous U)
    (hμ : ∀ g ∈ unitaryCompact ℝ 3, ∀ j : ℤ,
      blockFourierCoefficient 3 0 j H g =
        hA.μ j * blockFourierCoefficient 3 0 j f g)
    (hν : ∀ g ∈ unitaryCompact ℝ 3, ∀ j : ℤ,
      blockFourierCoefficient 3 1 j U g =
        hB.μ j * blockFourierCoefficient 3 1 j H g) :
    ∀ g ∈ unitaryCompact ℝ 3, ∀ j : ℤ, |j| < (z.weight.natAbs : ℤ) →
      blockFourierCoefficient 3 0 j U g = 0 := by
  have hparA := even_class_c_chA c z
  have hsignA := sign_class_c_chA c z
  rw [pairParity_comm c (chA z)] at hparA hsignA
  have hrecA := hA.recurrent
  have hrecB := hB.recurrent
  have hparam : c.exponent - (chA z).exponent + 1 + (z.weight.natAbs : ℂ) =
      c.exponent - (chB z).exponent + 1 := by
    rw [chA_exponent, chB_exponent]
    ring
  have hrecB' : IsRecurrent
      (c.exponent - (chA z).exponent + 1 + (z.weight.natAbs : ℂ))
      (c.parity.val : ℤ) (hB.μ) := by
    rw [hparam]
    exact isRecurrent_of_even hrecB (even_class_chB_c c z)
  have hland := (RealSwapLandingMirror.characterFirst_of_inducedFirst
    RealSwapLandingIntegral.inducedFirst) c z
    (c.exponent - (chA z).exponent + 1) (hA.μ) (hB.μ)
    f H U (isRecurrent_of_even hrecA hparA)
    (isSymmetric_of_even hA.symm
      hparA hsignA)
    hrecB'
    (isSymmetric_of_even hB.symm
      (even_class_chB_c c z) (sign_class_chB_c c z))
    hf hH hU hμ hν
  simpa only [Int.abs_eq_natAbs] using hland

end Landing

variable (d e : ComplexCharacterData) (h : FourCrossings d e)

/-! ## The six character crossings and their disjoint square -/

theorem dataBC : IsBlockFrobData 4 (expanded d e) (crossed d e) 1
    (pairParity (chA e) (chB d)) (sigma0 (chA e) (chB d))
    h.bc.μ :=
  swapData [.character (chA d)] [.character (chB e)] (chB d) (chA e) h.bc rfl

theorem dataAC : IsBlockFrobData 4 (crossed d e) (movedLeft d e) 0
    (pairParity (chA e) (chA d)) (sigma0 (chA e) (chA d))
    h.ac.μ :=
  swapData [] [.character (chB d), .character (chB e)] (chA d) (chA e) h.ac rfl

theorem dataBD : IsBlockFrobData 4 (movedLeft d e) (middle d e) 2
    (pairParity (chB e) (chB d)) (sigma0 (chB e) (chB d))
    h.bd.μ :=
  swapData [.character (chA e), .character (chA d)] [] (chB d) (chB e) h.bd rfl

theorem dataBD' : IsBlockFrobData 4 (crossed d e) (movedRight d e) 2
    (pairParity (chB e) (chB d)) (sigma0 (chB e) (chB d))
    h.bd.μ :=
  swapData [.character (chA d), .character (chA e)] [] (chB d) (chB e) h.bd rfl

theorem dataAC' : IsBlockFrobData 4 (movedRight d e) (middle d e) 0
    (pairParity (chA e) (chA d)) (sigma0 (chA e) (chA d))
    h.ac.μ :=
  swapData [] [.character (chB e), .character (chB d)] (chA d) (chA e) h.ac rfl

theorem dataAD : IsBlockFrobData 4 (middle d e) (expanded e d) 1
    (pairParity (chB e) (chA d)) (sigma0 (chB e) (chA d))
    h.ad.μ :=
  swapData [.character (chA e)] [.character (chB d)] (chA d) (chB e) h.ad rfl

/-- The two middle crossings act on disjoint coordinate pairs. -/
theorem middle_square (f : KF 4 (crossed d e)) :
    blockFrobMap (dataBD d e h) (blockFrobMap (dataAC d e h) f) =
      blockFrobMap (dataAC' d e h) (blockFrobMap (dataBD' d e h) f) :=
  blockFrobMap_commuting_square (Or.inl (by decide))
    (dataAC d e h) (dataBD' d e h) (dataBD d e h) (dataAC' d e h) f

/-- Forget the two original Fourier conditions and apply the four crossings. -/
def rawMap : KF 4 (source d e) →ₗ[ℂ] KF 4 (expanded e d) :=
  blockFrobMap (dataAD d e h) ∘ₗ blockFrobMap (dataBD d e h) ∘ₗ
    blockFrobMap (dataAC d e h) ∘ₗ blockFrobMap (dataBC d e h) ∘ₗ
      Submodule.inclusion (source_le_expanded d e)

/-- The first pair of crossings transports the first induction window once. -/
theorem first_window_once (f : KF 4 (source d e)) :
    ∀ g ∈ unitaryCompact ℝ 4, ∀ j : ℤ, |j| < (d.weight.natAbs : ℤ) →
      blockFourierCoefficient 4 1 j
        (blockFrobMap (dataAC d e h)
          (blockFrobMap (dataBC d e h) (Submodule.inclusion (source_le_expanded d e) f)) :
            Langlands.GeneralLinear 4 ℝ → ℂ) g = 0 := by
  let f0 : KF 4 (expanded d e) := Submodule.inclusion (source_le_expanded d e) f
  let H : KF 4 (crossed d e) := blockFrobMap (dataBC d e h) f0
  let U : KF 4 (movedLeft d e) := blockFrobMap (dataAC d e h) H
  let f' : KFin 4 ([] ++ lDC (chA e) d ++ [.character (chB e)]) :=
    ⟨(f : Langlands.GeneralLinear 4 ℝ → ℂ), source_le_keepFirst d e f.2⟩
  exact twoStep_landing_in_stages (n := 4) (a := 0) (r := 3)
    (pre := []) (ds := lDC (chA e) d) (post := [.character (chB e)])
    (by decide) rfl rfl (p := 1) (q := 0) (t := 1) (L := d.weight.natAbs)
    (by decide) (by decide) (by decide)
    h.bc.μ h.ac.μ
    (inducedFirst_landing (chA e) d h.bc h.ac) f'
    H.2.1.1.1 U.2.1.1.1
    (fun g hg j => blockFourierCoefficient_blockFrobMap (dataBC d e h) f0 hg j)
    (fun g hg j => blockFourierCoefficient_blockFrobMap (dataAC d e h) H hg j)

/-- Both induced-first landings put the first induction window in its final position. -/
theorem first_window (f : KF 4 (source d e)) :
    ∀ g ∈ unitaryCompact ℝ 4, ∀ j : ℤ, |j| < (d.weight.natAbs : ℤ) →
      blockFourierCoefficient 4 2 j
        (rawMap d e h f : Langlands.GeneralLinear 4 ℝ → ℂ) g = 0 := by
  let f0 : KF 4 (expanded d e) := Submodule.inclusion (source_le_expanded d e) f
  let f1 : KF 4 (crossed d e) := blockFrobMap (dataBC d e h) f0
  let f2 : KF 4 (movedLeft d e) := blockFrobMap (dataAC d e h) f1
  let H : KF 4 (middle d e) := blockFrobMap (dataBD d e h) f2
  let U : KF 4 (expanded e d) := blockFrobMap (dataAD d e h) H
  let f' : KFin 4 ([.character (chA e)] ++ lDC (chB e) d ++ []) :=
    ⟨(f2 : Langlands.GeneralLinear 4 ℝ → ℂ),
      mem_firstMoved d e f2 (first_window_once d e h f)⟩
  exact twoStep_landing_in_stages (n := 4) (a := 1) (r := 3)
    (pre := [.character (chA e)]) (ds := lDC (chB e) d) (post := [])
    (by decide) rfl rfl (p := 1) (q := 0) (t := 1) (L := d.weight.natAbs)
    (by decide) (by decide) (by decide)
    h.bd.μ h.ad.μ
    (inducedFirst_landing (chB e) d h.bd h.ad) f'
    H.2.1.1.1 U.2.1.1.1
    (fun g hg j => blockFourierCoefficient_blockFrobMap (dataBD d e h) f2 hg j)
    (fun g hg j => blockFourierCoefficient_blockFrobMap (dataAD d e h) H hg j)

/-- On the other path, the first pair of crossings transports the second window once. -/
theorem second_window_once (f : KF 4 (source d e)) :
    ∀ g ∈ unitaryCompact ℝ 4, ∀ j : ℤ, |j| < (e.weight.natAbs : ℤ) →
      blockFourierCoefficient 4 1 j
        (blockFrobMap (dataBD' d e h)
          (blockFrobMap (dataBC d e h) (Submodule.inclusion (source_le_expanded d e) f)) :
            Langlands.GeneralLinear 4 ℝ → ℂ) g = 0 := by
  let f0 : KF 4 (expanded d e) := Submodule.inclusion (source_le_expanded d e) f
  let H : KF 4 (crossed d e) := blockFrobMap (dataBC d e h) f0
  let U : KF 4 (movedRight d e) := blockFrobMap (dataBD' d e h) H
  let f' : KFin 4 ([.character (chA d)] ++ lCD (chB d) e ++ []) :=
    ⟨(f : Langlands.GeneralLinear 4 ℝ → ℂ), source_le_keepSecond d e f.2⟩
  exact twoStep_landing_in_stages (n := 4) (a := 1) (r := 3)
    (pre := [.character (chA d)]) (ds := lCD (chB d) e) (post := [])
    (by decide) rfl rfl (p := 0) (q := 1) (t := 0) (L := e.weight.natAbs)
    (by decide) (by decide) (by decide)
    h.bc.μ h.bd.μ
    (characterFirst_landing (chB d) e h.bc h.bd) f'
    H.2.1.1.1 U.2.1.1.1
    (fun g hg j => blockFourierCoefficient_blockFrobMap (dataBC d e h) f0 hg j)
    (fun g hg j => blockFourierCoefficient_blockFrobMap (dataBD' d e h) H hg j)

/-- The disjoint square identifies the second-window path with the chosen map. -/
theorem second_window (f : KF 4 (source d e)) :
    ∀ g ∈ unitaryCompact ℝ 4, ∀ j : ℤ, |j| < (e.weight.natAbs : ℤ) →
      blockFourierCoefficient 4 0 j
        (rawMap d e h f : Langlands.GeneralLinear 4 ℝ → ℂ) g = 0 := by
  let f0 : KF 4 (expanded d e) := Submodule.inclusion (source_le_expanded d e) f
  let f1 : KF 4 (crossed d e) := blockFrobMap (dataBC d e h) f0
  let f2 : KF 4 (movedRight d e) := blockFrobMap (dataBD' d e h) f1
  let H : KF 4 (middle d e) := blockFrobMap (dataAC' d e h) f2
  let U : KF 4 (expanded e d) := blockFrobMap (dataAD d e h) H
  let f' : KFin 4 ([] ++ lCD (chA d) e ++ [.character (chB d)]) :=
    ⟨(f2 : Langlands.GeneralLinear 4 ℝ → ℂ),
      mem_secondMoved d e f2 (second_window_once d e h f)⟩
  have hland := twoStep_landing_in_stages (n := 4) (a := 0) (r := 3)
    (pre := []) (ds := lCD (chA d) e) (post := [.character (chB d)])
    (by decide) rfl rfl (p := 0) (q := 1) (t := 0) (L := e.weight.natAbs)
    (by decide) (by decide) (by decide)
    h.ac.μ h.ad.μ
    (characterFirst_landing (chA d) e h.ac h.ad) f'
    H.2.1.1.1 U.2.1.1.1
    (fun g hg j => blockFourierCoefficient_blockFrobMap (dataAC' d e h) f2 hg j)
    (fun g hg j => blockFourierCoefficient_blockFrobMap (dataAD d e h) H hg j)
  have heq : rawMap d e h f = U := by
    change blockFrobMap (dataAD d e h)
      (blockFrobMap (dataBD d e h) (blockFrobMap (dataAC d e h) f1)) =
        blockFrobMap (dataAD d e h)
          (blockFrobMap (dataAC' d e h) (blockFrobMap (dataBD' d e h) f1))
    rw [middle_square]
  rw [heq]
  exact hland

/-- Compact vanishing for both windows gives membership in the actual target module. -/
theorem rawMap_mem_target (f : KF 4 (source d e)) :
    (rawMap d e h f : Langlands.GeneralLinear 4 ℝ → ℂ) ∈ KF 4 (target d e) := by
  refine ⟨RealBlockPosition.mem_realStandardModule_of_unitaryCompact
    (N := 4) (ds := target d e) rfl ?_ ?_, (rawMap d e h f).2.2⟩
  · rw [← pos_expanded e d]
    exact (rawMap d e h f).2.1.1
  · intro p z hz j hj g hg
    rcases p with _ | _ | _ | _ | p
    · simp only [realInducedBlockAt, Option.some.injEq] at hz
      subst z
      exact second_window d e h f g hg j (by simpa only [Int.abs_eq_natAbs] using hj)
    · simp [realInducedBlockAt] at hz
    · simp only [realInducedBlockAt, Option.some.injEq] at hz
      subst z
      exact first_window d e h f g hg j (by simpa only [Int.abs_eq_natAbs] using hj)
    all_goals simp [realInducedBlockAt] at hz

/-- All four recurrent factors and their composite intertwine exactly. -/
theorem rawMap_modulo :
    IsRealIntertwinerModulo 4 (source d e) (expanded e d) ⊥ (rawMap d e h) := by
  have hinc : IsRealIntertwinerModulo 4 (source d e) (expanded d e) ⊥
      (Submodule.inclusion (source_le_expanded d e)) :=
    modulo_bot_of_coe (modulo_id (source d e)) (fun _ => rfl)
  exact modulo_comp_bot
    (swap_modulo [.character (chA e)] [.character (chB d)]
      (chA d) (chB e) h.ad rfl)
    (modulo_comp_bot
      (swap_modulo [.character (chA e), .character (chA d)] []
        (chB d) (chB e) h.bd rfl)
      (modulo_comp_bot
        (swap_modulo [] [.character (chB d), .character (chB e)]
          (chA d) (chA e) h.ac rfl)
        (modulo_comp_bot
          (swap_modulo [.character (chA d)] [.character (chB e)]
            (chB d) (chA e) h.bc rfl) hinc)))

/-- The recurrent composite corestricted to the actual two-block target. -/
def recurrentMap : KF 4 (source d e) →ₗ[ℂ] KF 4 (target d e) :=
  LinearMap.codRestrict (KF 4 (target d e))
    ((KF 4 (expanded e d)).subtype ∘ₗ rawMap d e h) (rawMap_mem_target d e h)

/-- Corestriction preserves exact compact and Lie intertwining. -/
theorem recurrentMap_modulo :
    IsRealIntertwinerModulo 4 (source d e) (target d e) ⊥ (recurrentMap d e h) :=
  modulo_bot_of_coe (rawMap_modulo d e h) (fun _ => rfl)

end RealInducedSwapRecurrent
end Langlands.Archimedean

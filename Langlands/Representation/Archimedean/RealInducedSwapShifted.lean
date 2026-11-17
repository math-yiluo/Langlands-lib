import Langlands.Representation.Archimedean.RealInducedSwapRecurrent

/-!
# Four crossings with a common recurrence shift

The source and target exponents stay fixed. A common additive shift in the four
recurrence parameters preserves both target induction windows. No assertion about
intertwining the fixed Lie actions is made away from zero shift.
-/

noncomputable section

open scoped TensorProduct Matrix Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean
namespace RealInducedSwapShifted

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open RealBlockFrobeniusMap RealBlockPosition RealBlockMultiplier RealCharacterPair
open RealCharacterPairReducible RealBlockJacquet RealStandardFiltration
open RealCharacterInducedSwap RealCharacterInducedPushforward
open InductionStages RealBlockMultiplierSlices RealDisjointBlockMultipliers
open RealInducedSwapGeneric

attribute [local instance 100] LieRing.ofAssociativeRing

/-- A symmetric sequence recurrent at the source exponent difference plus a shift. -/
structure Crossing (x y : RealCharacterData) (ζ : ℂ) where
  μ : ℤ → ℂ
  symm : IsSymmetric (pairParity y x) (sigma0 y x) μ
  recurrent : IsRecurrent (x.exponent - y.exponent + 1 + ζ) (pairParity y x) μ

/-- Four symmetric sequences whose recurrence parameters have the same shift. -/
structure FourCrossings (d e : ComplexCharacterData) (ζ : ℂ) where
  bc : Crossing (chB d) (chA e) ζ
  ac : Crossing (chA d) (chA e) ζ
  bd : Crossing (chB d) (chB e) ζ
  ad : Crossing (chA d) (chB e) ζ

variable {ζ : ℂ}

section Swap

variable {n : ℕ} (pre post : List RealBlock) (x y : RealCharacterData) (h : Crossing x y ζ)

/-- Frobenius data for a symmetric crossing in an arbitrary context. -/
theorem swapData
    (hr : realRank (pre ++ .character x :: .character y :: post) = n) :
    IsBlockFrobData n (pre ++ .character x :: .character y :: post)
      (pre ++ .character y :: .character x :: post) (realRank pre)
      (pairParity y x) (sigma0 y x) h.μ := by
  simpa only [dc, mid_pair] using
    (data_swap (c := y) (d := x)
      (by simpa only [mid_pair] using realRank_dc_mid hr) h.symm)

end Swap

section Landing

variable (c : RealCharacterData) (z : ComplexCharacterData)

/-- The induced-first landing for two arbitrary recurrent crossings. -/
theorem inducedFirst_landing
    (hB : Crossing (chB z) c ζ)
    (hA : Crossing (chA z) c ζ)
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
  have hparam : (chB z).exponent - c.exponent + 1 + ζ + (z.weight.natAbs : ℂ) =
      (chA z).exponent - c.exponent + 1 + ζ := by
    rw [chA_exponent, chB_exponent]
    ring
  have hrecA' : IsRecurrent
      ((chB z).exponent - c.exponent + 1 + ζ + (z.weight.natAbs : ℂ))
      ((z.weight.natAbs + 1 + c.parity.val : ℕ) : ℤ) (hA.μ) := by
    rw [hparam]
    exact isRecurrent_of_even hrecA (even_class_c_chA c z)
  have hland := RealSwapLandingIntegral.inducedFirst c z
    ((chB z).exponent - c.exponent + 1 + ζ) (hA.μ) (hB.μ)
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
    (hA : Crossing c (chA z) ζ)
    (hB : Crossing c (chB z) ζ)
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
  have hparam : c.exponent - (chA z).exponent + 1 + ζ + (z.weight.natAbs : ℂ) =
      c.exponent - (chB z).exponent + 1 + ζ := by
    rw [chA_exponent, chB_exponent]
    ring
  have hrecB' : IsRecurrent
      (c.exponent - (chA z).exponent + 1 + ζ + (z.weight.natAbs : ℂ))
      (c.parity.val : ℤ) (hB.μ) := by
    rw [hparam]
    exact isRecurrent_of_even hrecB (even_class_chB_c c z)
  have hland := (RealSwapLandingMirror.characterFirst_of_inducedFirst
    RealSwapLandingIntegral.inducedFirst) c z
    (c.exponent - (chA z).exponent + 1 + ζ) (hA.μ) (hB.μ)
    f H U (isRecurrent_of_even hrecA hparA)
    (isSymmetric_of_even hA.symm
      hparA hsignA)
    hrecB'
    (isSymmetric_of_even hB.symm
      (even_class_chB_c c z) (sign_class_chB_c c z))
    hf hH hU hμ hν
  simpa only [Int.abs_eq_natAbs] using hland

end Landing

variable (d e : ComplexCharacterData) (h : FourCrossings d e ζ)

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

/-- The shifted composite corestricted to the actual two-block target. -/
def shiftedMap : KF 4 (source d e) →ₗ[ℂ] KF 4 (target d e) :=
  LinearMap.codRestrict (KF 4 (target d e))
    ((KF 4 (expanded e d)).subtype ∘ₗ rawMap d e h) (rawMap_mem_target d e h)

/-- The shifted map commutes with the compact action for every shift. -/
theorem rawMap_rightTranslation (k : Matrix.unitaryGroup (Fin 4) ℝ)
    (f : KF 4 (source d e)) :
    rawMap d e h (realStandardRep 4 (source d e) k f) =
      realStandardRep 4 (expanded e d) k (rawMap d e h f) := by
  have hinc :
      Submodule.inclusion (source_le_expanded d e)
          (realStandardRep 4 (source d e) k f) =
        realStandardRep 4 (expanded d e) k
          (Submodule.inclusion (source_le_expanded d e) f) := by
    apply Subtype.ext
    rfl
  change blockFrobMap (dataAD d e h)
    (blockFrobMap (dataBD d e h)
      (blockFrobMap (dataAC d e h)
        (blockFrobMap (dataBC d e h)
          (Submodule.inclusion (source_le_expanded d e)
            (realStandardRep 4 (source d e) k f))))) = _
  rw [hinc, blockFrobMap_rightTranslation, blockFrobMap_rightTranslation,
    blockFrobMap_rightTranslation, blockFrobMap_rightTranslation]
  rfl

theorem shiftedMap_rightTranslation (k : Matrix.unitaryGroup (Fin 4) ℝ)
    (f : KF 4 (source d e)) :
    shiftedMap d e h (realStandardRep 4 (source d e) k f) =
      realStandardRep 4 (target d e) k (shiftedMap d e h f) := by
  apply Subtype.ext
  exact congrArg
    (fun v : KF 4 (expanded e d) => (v : Langlands.GeneralLinear 4 ℝ → ℂ))
    (rawMap_rightTranslation d e h k f)

/-- With zero shift, the supplied sequences are ordinary recurrent crossings. -/
def FourCrossings.toRecurrent (h₀ : FourCrossings d e 0) :
    RealInducedSwapRecurrent.FourCrossings d e where
  bc := ⟨h₀.bc.μ, h₀.bc.symm, by simpa only [add_zero] using h₀.bc.recurrent⟩
  ac := ⟨h₀.ac.μ, h₀.ac.symm, by simpa only [add_zero] using h₀.ac.recurrent⟩
  bd := ⟨h₀.bd.μ, h₀.bd.symm, by simpa only [add_zero] using h₀.bd.recurrent⟩
  ad := ⟨h₀.ad.μ, h₀.ad.symm, by simpa only [add_zero] using h₀.ad.recurrent⟩

/-- At zero shift, the map intertwines the fixed compact and Lie actions. -/
theorem shiftedMap_zero_modulo (h₀ : FourCrossings d e 0) :
    IsRealIntertwinerModulo 4 (source d e) (target d e) ⊥ (shiftedMap d e h₀) :=
  modulo_bot_of_coe
    (RealInducedSwapRecurrent.recurrentMap_modulo d e (h₀.toRecurrent d e))
    (fun _ => rfl)

end RealInducedSwapShifted
end Langlands.Archimedean

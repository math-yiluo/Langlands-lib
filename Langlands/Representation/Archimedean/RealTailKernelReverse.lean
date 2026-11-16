import Langlands.Representation.Archimedean.RealTailKernelInStages

/-! # The reverse ascending tail-kernel step -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

namespace RealTailKernelReverse

open RealBlockFrobeniusMap RealBlockMultiplier RealCharacterPair RealCharacterPairReducible
open RealCharacterInducedPushforward RealStandardFiltration RealSwapLandingMirror
open RealSwapFLanding RealBlockPosition GramFormula RealBlockJacquet

/-- Left reflection by the compact involution reversing the two coordinate rotations. -/
def reflect : (Langlands.GeneralLinear 3 ℝ → ℂ) →ₗ[ℂ]
    (Langlands.GeneralLinear 3 ℝ → ℂ) :=
  LinearMap.funLeft ℂ ℂ fun x => mirrorUnit * x

@[simp] theorem reflect_apply (F : Langlands.GeneralLinear 3 ℝ → ℂ)
    (x : Langlands.GeneralLinear 3 ℝ) : reflect F x = F (mirrorUnit * x) := rfl

theorem continuous_reflect {F : Langlands.GeneralLinear 3 ℝ → ℂ} (hF : Continuous F) :
    Continuous (reflect F) := hF.comp (continuous_const.mul continuous_id)

theorem kFinite_reflect {F : Langlands.GeneralLinear 3 ℝ → ℂ}
    (hF : F ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear 3 ℝ))
      (unitaryCompact ℝ 3)) :
    reflect F ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear 3 ℝ))
      (unitaryCompact ℝ 3) := by
  rw [mem_kFiniteVectors_iff] at hF ⊢
  have hle : Submodule.span ℂ (Set.range fun k : unitaryCompact ℝ 3 =>
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear 3 ℝ)
        (k : Langlands.GeneralLinear 3 ℝ) (reflect F)) ≤
      (Submodule.span ℂ (Set.range fun k : unitaryCompact ℝ 3 =>
        Whittaker.rightTranslation ℂ (Langlands.GeneralLinear 3 ℝ)
          (k : Langlands.GeneralLinear 3 ℝ) F)).map reflect := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    refine ⟨_, Submodule.subset_span ⟨k, rfl⟩, ?_⟩
    funext x
    exact congrArg F (mul_assoc _ _ _)
  exact Submodule.finiteDimensional_of_le hle

variable (c : RealCharacterData) (d : ComplexCharacterData) (sb : Fin 2)

/-- The target of the high-mode projection at position zero. -/
abbrev lG0 : List RealBlock :=
  [.character (RealJacquetFrobenius.charData (chiB d sb).parity (chiA d sb).exponent),
   .character (RealJacquetFrobenius.charData (chiA d sb).parity (chiB d sb).exponent),
   .character c]

theorem dataG0 : IsBlockFrobData 3 (lZ c d sb) (lG0 c d sb) 0
    (pairParity (chiB d sb) (chiA d sb)) 1 (highIndicator d) := by
  refine IsBlockFrobData.of_mid (pre := []) (post := [.character c])
    (ws := [.character (chiB d sb), .character (chiA d sb)])
    (ws' := [.character
        (RealJacquetFrobenius.charData (chiB d sb).parity (chiA d sb).exponent),
      .character (RealJacquetFrobenius.charData (chiA d sb).parity (chiB d sb).exponent)])
    rfl rfl rfl rfl rfl ?_ (isSymmetric_highIndicator d _) ?_ ?_ ?_
  · rw [realPositionCharacter_neg_one, realPositionCharacter_neg_one,
      neg_one_pow_pairParity']
    rfl
  · rw [realPositionCharacter_neg_one, mul_one]
    rfl
  · rw [realPositionCharacter_neg_one, mul_one]
    rfl
  · intro e he
    simp [realInducedBlockAt] at he

/-- The character needed for sign equivariance after reflecting the high projection. -/
def cPR : RealCharacterData :=
  RealJacquetFrobenius.charData (fin2 (c.parity.val + sb.val)) c.exponent

theorem reflected_sign (G : KF 3 (lG0 c d sb)) (a : Fin 3 → ℝˣ)
    (κ : Matrix.unitaryGroup (Fin 3) ℝ) :
    reflect (G : Langlands.GeneralLinear 3 ℝ → ℂ)
        (Unitary.toUnits (PrincipalSeriesExtension.signDiagonal (fun i => (a i : ℝ)) * κ)) =
      principalSeriesCharacter ℝ 3
          (realPositionCharacter [.character (cPR c sb), .induced d])
          (fun i => signUnit (a i)) *
        sgnDet 3 (Unitary.toUnits
          (PrincipalSeriesExtension.signDiagonal (fun i => (a i : ℝ)))) ^ sb.val *
        reflect (G : Langlands.GeneralLinear 3 ℝ → ℂ) (Unitary.toUnits κ) := by
  have hm : mirrorUnit * Unitary.toUnits
      (PrincipalSeriesExtension.signDiagonal (fun i => (a i : ℝ)) * κ) =
      Unitary.toUnits (PrincipalSeriesExtension.signDiagonal
        (fun i => ((![a 2, a 1, a 0] : Fin 3 → ℝˣ) i : ℝ)) * (mirror * κ)) := by
    rw [mirrorUnit, ← map_mul, ← mul_assoc, mirror_mul_signDiagonal, mul_assoc]
  simp only [reflect_apply]
  rw [hm, PartialJacquet.signDiagonal_toUnits, G.2.1.1.2,
    JacquetKernel.principalSeriesCharacter_sign,
    JacquetKernel.principalSeriesCharacter_sign,
    RealCharacterInducedPushforward.sgnDet_signDiagonal, ← Finset.prod_pow,
    ← Finset.prod_mul_distrib, map_mul]

  congr 1
  rw [Fin.prod_univ_three, Fin.prod_univ_three]
  simp only [posChar_signUnit]
  have hpow (i : Fin 3) :
      ((signReal (a i : ℝ) : ℝ) : ℂ) ^
          (realPositionSign (lG0 c d sb) (2 - i.val)).val =
        ((signReal (a i : ℝ) : ℝ) : ℂ) ^
            (realPositionSign [.character (cPR c sb), .induced d] i.val).val *
          ((signReal (a i : ℝ) : ℝ) : ℂ) ^ sb.val := by
    refine pow_eq_pow_mul_pow_of_sq (signReal_sq _) ?_
    fin_cases i <;>
      simp [realPositionSign, cPR, lG0, chiA, chiB, RealJacquetFrobenius.charData] <;> omega
  have h0 := hpow 0
  have h1 := hpow 1
  have h2 := hpow 2
  norm_num [lG0, realPositionSign, chiA, chiB, RealJacquetFrobenius.charData] at h0 h1 h2 ⊢
  rw [h0, h1]
  ring


/-- Reverse swap across the lower character of the ascending pair. -/
theorem dataR1 {μ : ℤ → ℂ}
    (hs : IsSymmetric (pairParity (chiB d sb) c) (sigma0 (chiB d sb) c) μ) :
    IsBlockFrobData 3 (lX c d sb) (lY c d sb) 0 (pairParity (chiB d sb) c)
      (sigma0 (chiB d sb) c) μ :=
  data_swap (pre := []) (post := [.character (chiA d sb)])
    (c := chiB d sb) (d := c) rfl hs

/-- Reverse swap across the upper character of the ascending pair. -/
theorem dataR2 {μ : ℤ → ℂ}
    (hs : IsSymmetric (pairParity (chiA d sb) c) (sigma0 (chiA d sb) c) μ) :
    IsBlockFrobData 3 (lY c d sb) (lZ c d sb) 1 (pairParity (chiA d sb) c)
      (sigma0 (chiA d sb) c) μ :=
  data_swap (pre := [.character (chiB d sb)]) (post := [])
    (c := chiA d sb) (d := c) rfl hs

theorem even_R2_class :
    Even (pairParity (chiA d sb) c -
      ((d.weight.natAbs + 1 + (cPR c sb).parity.val : ℕ) : ℤ)) := by
  rw [Int.even_iff]
  simp only [pairParity, chiA, cPR, RealJacquetFrobenius.charData, fin2_val]
  omega

theorem sigma_R2 :
    sigma0 (chiA d sb) c = (-1) ^ (d.weight.natAbs + 1 + (cPR c sb).parity.val) := by
  apply RealCharacterInducedPushforward.neg_one_pow_congr
  simp only [pairParity, chiA, cPR, RealJacquetFrobenius.charData, fin2_val]
  omega

theorem R1_class : pairParity (chiB d sb) c = ((cPR c sb).parity.val : ℤ) := by
  simp only [pairParity, chiB, cPR, RealJacquetFrobenius.charData, fin2_val, Nat.add_comm]

theorem sigma_R1 : sigma0 (chiB d sb) c = (-1) ^ (cPR c sb).parity.val := by
  rw [sigma0, R1_class]
  rfl

/-- Two reverse recurrent swaps preserve the ascending tail kernel. -/
theorem kernel_step (hl : 0 < d.weight.natAbs) {μ₀ μ₁ : ℤ → ℂ}
    (hQ1 : IsBlockFrobData 3 (lX c d sb) (lY c d sb) 0
      (pairParity (chiB d sb) c) (sigma0 (chiB d sb) c) μ₀)
    (hQ2 : IsBlockFrobData 3 (lY c d sb) (lZ c d sb) 1
      (pairParity (chiA d sb) c) (sigma0 (chiA d sb) c) μ₁)
    (hμ₀ : IsRecurrent (c.exponent - (chiB d sb).exponent + 1)
      (pairParity (chiB d sb) c) μ₀)
    (hμ₁ : IsRecurrent (c.exponent - (chiA d sb).exponent + 1)
      (pairParity (chiA d sb) c) μ₁)
    (z : KF 3 (lX c d sb)) (hz : blockFrobMap (dataD1 c d sb hl) z = 0) :
    blockFrobMap (dataT0 c d sb hl) (blockFrobMap hQ2 (blockFrobMap hQ1 z)) = 0 := by
  have hεba := pairParity_eq (chiB d sb) (chiA d sb)
  have hpar := even_pairParity_chiB_chiA d sb
  have hσ := neg_one_pow_sq_fin (chiA d sb).parity
  have habs : |d.weight| = (d.weight.natAbs : ℤ) := Int.abs_eq_natAbs d.weight
  have hf0 : ∀ j : ℤ, |d.weight| ≤ |j| → ∀ x ∈ unitaryCompact ℝ 3,
      blockFourierCoefficient 3 1 j (z : Langlands.GeneralLinear 3 ℝ → ℂ) x = 0 := by
    intro j hj x hx
    by_cases hje : Even (j - pairParity (chiB d sb) (chiA d sb))
    · have e := blockFourierCoefficient_blockFrobMap (dataD1 c d sb hl) z hx j
      rw [hz, ZeroMemClass.coe_zero, blockFourierCoefficient_zero] at e
      refine (mul_eq_zero.mp e.symm).resolve_left
        ((tailMultiplier_ne_zero_iff hl hεba hpar hσ hje).mpr ?_)
      rw [habs] at hj
      rcases hj.lt_or_eq with hlt | heq
      · exact hlt
      · exact absurd heq.le (not_le.mpr (abs_lt_of_parity hpar hje heq.symm.le))
    · exact blockFourierCoefficient_eq_zero_of_not_even (dataD1 c d sb hl).lt
        (dataD1 c d sb hl).par z hje x
  have hδ : c.exponent - (chiA d sb).exponent + 1 + (d.weight.natAbs : ℂ) =
      c.exponent - (chiB d sb).exponent + 1 := by
    rw [chiA_exponent, chiB_exponent]
    ring
  have hμ₁' : IsRecurrent
      (c.exponent - (chiA d sb).exponent + 1 + (d.weight.natAbs : ℂ))
      ((cPR c sb).parity.val : ℤ) μ₀ := by
    rw [hδ, ← R1_class c d sb]
    exact hμ₀
  set g₁ := blockFrobMap hQ1 z with hg₁
  set g := blockFrobMap hQ2 g₁ with hg
  set G := blockFrobMap (dataG0 c d sb) g with hG
  have hhigh := RealSwapFLanding.highModes_eq_zero
    (characterFirst_of_inducedFirst RealSwapLandingIntegral.inducedFirst)
    (cPR c sb) d (c.exponent - (chiA d sb).exponent + 1) μ₁ μ₀
    (isRecurrent_of_even hμ₁ (even_R2_class c d sb))
    (isSymmetric_of_even hQ2.sym (even_R2_class c d sb) (sigma_R2 c d sb))
    hμ₁' (by simpa only [R1_class, sigma_R1] using hQ1.sym) sb.val
    (continuous_reflect (continuous_coe z)) (continuous_reflect (continuous_coe g₁))
    (continuous_reflect (continuous_coe g)) (continuous_reflect (continuous_coe G))
    (kFinite_reflect z.2.2) (kFinite_reflect g₁.2.2)
    (kFinite_reflect g.2.2) (kFinite_reflect G.2.2)
    (fun j hj x hx => by
      rw [show reflect (z : Langlands.GeneralLinear 3 ℝ → ℂ) =
        (fun y => (z : Langlands.GeneralLinear 3 ℝ → ℂ) (mirrorUnit * y)) from rfl,
        blockFourierCoefficient_comp_mirror mirror_mul_blockRotation_zero]
      exact hf0 j hj _ ((unitaryCompact ℝ 3).mul_mem mirrorUnit_mem hx))
    (fun j x hx => by
      change blockFourierCoefficient 3 1 j (fun y =>
        (g₁ : Langlands.GeneralLinear 3 ℝ → ℂ) (mirrorUnit * y)) x =
        μ₀ j * blockFourierCoefficient 3 1 j (fun y =>
          (z : Langlands.GeneralLinear 3 ℝ → ℂ) (mirrorUnit * y)) x
      rw [blockFourierCoefficient_comp_mirror mirror_mul_blockRotation_one,
        blockFourierCoefficient_comp_mirror mirror_mul_blockRotation_one]
      exact blockFourierCoefficient_blockFrobMap hQ1 z
        ((unitaryCompact ℝ 3).mul_mem mirrorUnit_mem hx) j)
    (fun j x hx => by
      change blockFourierCoefficient 3 0 j (fun y =>
        (g : Langlands.GeneralLinear 3 ℝ → ℂ) (mirrorUnit * y)) x =
        μ₁ j * blockFourierCoefficient 3 0 j (fun y =>
          (g₁ : Langlands.GeneralLinear 3 ℝ → ℂ) (mirrorUnit * y)) x
      rw [blockFourierCoefficient_comp_mirror mirror_mul_blockRotation_zero,
        blockFourierCoefficient_comp_mirror mirror_mul_blockRotation_zero]
      exact blockFourierCoefficient_blockFrobMap hQ2 g₁
        ((unitaryCompact ℝ 3).mul_mem mirrorUnit_mem hx) j)
    (fun j hj x hx => by
      change blockFourierCoefficient 3 1 j (fun y =>
        (G : Langlands.GeneralLinear 3 ℝ → ℂ) (mirrorUnit * y)) x =
        blockFourierCoefficient 3 1 j (fun y =>
          (g : Langlands.GeneralLinear 3 ℝ → ℂ) (mirrorUnit * y)) x
      rw [blockFourierCoefficient_comp_mirror mirror_mul_blockRotation_one,
        blockFourierCoefficient_comp_mirror mirror_mul_blockRotation_one,
        hG, blockFourierCoefficient_blockFrobMap (dataG0 c d sb) g
          ((unitaryCompact ℝ 3).mul_mem mirrorUnit_mem hx) j,
        highIndicator, ite_eq_left hj, one_mul])
    (fun j hj x hx => by
      change blockFourierCoefficient 3 1 j (fun y =>
        (G : Langlands.GeneralLinear 3 ℝ → ℂ) (mirrorUnit * y)) x = 0
      rw [blockFourierCoefficient_comp_mirror mirror_mul_blockRotation_one,
        hG, blockFourierCoefficient_blockFrobMap (dataG0 c d sb) g
          ((unitaryCompact ℝ 3).mul_mem mirrorUnit_mem hx) j,
        highIndicator, ite_eq_right (not_le.mpr hj), zero_mul])
    (reflected_sign c d sb G)
  have hhigh' : ∀ j : ℤ, |d.weight| ≤ |j| → ∀ x ∈ unitaryCompact ℝ 3,
      blockFourierCoefficient 3 0 j (g : Langlands.GeneralLinear 3 ℝ → ℂ) x = 0 := by
    intro j hj x hx
    have h := hhigh j hj (mirrorUnit * x)
      ((unitaryCompact ℝ 3).mul_mem mirrorUnit_mem hx)
    change blockFourierCoefficient 3 1 j (fun y =>
      (g : Langlands.GeneralLinear 3 ℝ → ℂ) (mirrorUnit * y)) (mirrorUnit * x) = 0 at h
    rwa [blockFourierCoefficient_comp_mirror mirror_mul_blockRotation_one,
      mirrorUnit_mul_mirrorUnit_mul] at h
  refine eq_of_blockFourierCoefficient_eq (dataT0 c d sb hl).lt fun j x hx => ?_
  rw [ZeroMemClass.coe_zero, blockFourierCoefficient_zero]
  by_cases hj : |d.weight| ≤ |j|
  · rw [blockFourierCoefficient_blockFrobMap (dataT0 c d sb hl) g hx j,
      hhigh' j hj x hx, mul_zero]
  · exact (blockFrobMap (dataT0 c d sb hl) g).2.1.2 0 (dP d sb) rfl j
      (by rw [dP_abs_weight, ← habs]; exact not_le.mp hj) x

/-- Reverse tail-kernel compatibility in arbitrary surrounding blocks. -/
theorem kernel_step_inStages {n : ℕ} (pre post : List RealBlock)
    (hn : realRank pre + 3 + realRank post = n)
    (hl : 0 < d.weight.natAbs) {μ₀ μ₁ : ℤ → ℂ}
    (hQ1 : IsBlockFrobData n (pre ++ lX c d sb ++ post) (pre ++ lY c d sb ++ post)
      (realRank pre) (pairParity (chiB d sb) c) (sigma0 (chiB d sb) c) μ₀)
    (hQ2 : IsBlockFrobData n (pre ++ lY c d sb ++ post) (pre ++ lZ c d sb ++ post)
      (realRank pre + 1) (pairParity (chiA d sb) c) (sigma0 (chiA d sb) c) μ₁)
    (hD : IsBlockFrobData n (pre ++ lX c d sb ++ post) (pre ++ lV c d sb ++ post)
      (realRank pre + 1) (pairParity (chiB d sb) (chiA d sb))
      ((-1) ^ (chiA d sb).parity.val)
      (tailMultiplier d.weight.natAbs (pairParity (chiB d sb) (chiA d sb))
        ((-1) ^ (chiA d sb).parity.val)))
    (hT : IsBlockFrobData n (pre ++ lZ c d sb ++ post) (pre ++ lW c d sb ++ post)
      (realRank pre) (pairParity (chiB d sb) (chiA d sb))
      ((-1) ^ (chiA d sb).parity.val)
      (tailMultiplier d.weight.natAbs (pairParity (chiB d sb) (chiA d sb))
        ((-1) ^ (chiA d sb).parity.val)))
    (hμ₀ : IsRecurrent (c.exponent - (chiB d sb).exponent + 1)
      (pairParity (chiB d sb) c) μ₀)
    (hμ₁ : IsRecurrent (c.exponent - (chiA d sb).exponent + 1)
      (pairParity (chiA d sb) c) μ₁)
    (z : KF n (pre ++ lX c d sb ++ post)) (hz : blockFrobMap hD z = 0) :
    blockFrobMap hT (blockFrobMap hQ2 (blockFrobMap hQ1 z)) = 0 := by
  have h : realRank pre + 3 ≤ n := by omega
  have hrX : realRank (lX c d sb) = 3 := rfl
  have hrY : realRank (lY c d sb) = 3 := rfl
  have hrZ : realRank (lZ c d sb) = 3 := rfl
  have hrV : realRank (lV c d sb) = 3 := rfl
  have hrW : realRank (lW c d sb) = 3 := rfl
  have hQ1' := dataR1 c d sb hQ1.sym
  have hQ2' := dataR2 c d sb hQ2.sym
  apply RealTailKernelInStages.eq_zero_of_slices h rfl hrW
  intro κ
  rw [RealTailKernelInStages.frob_slice h rfl hrZ hrW
      (by simpa only [Nat.add_zero] using hT) (dataT0 c d sb hl),
    RealTailKernelInStages.frob_slice h rfl hrY hrZ hQ2 hQ2',
    RealTailKernelInStages.frob_slice h rfl hrX hrY
      (by simpa only [Nat.add_zero] using hQ1) hQ1']
  apply kernel_step c d sb hl hQ1' hQ2' hμ₀ hμ₁
  rw [← RealTailKernelInStages.frob_slice h rfl hrX hrV hD (dataD1 c d sb hl),
    hz, map_zero]

end RealTailKernelReverse

open RealTailKernelReverse RealBlockFrobeniusMap RealBlockMultiplier RealCharacterPair
open RealCharacterInducedPushforward RealStandardFiltration RealCharacterPairReducible

/-- The reverse ascending tail-kernel statement with explicit Frobenius data. -/
def RealTailKernelReverseStatement : Prop :=
  ∀ {n : ℕ} (c : RealCharacterData) (d : ComplexCharacterData) (sb : Fin 2)
    (pre post : List RealBlock)
    (_hn : realRank pre + 3 + realRank post = n)
    (_hl : 0 < d.weight.natAbs) {μ₀ μ₁ : ℤ → ℂ}
    (hQ1 : IsBlockFrobData n (pre ++ lX c d sb ++ post) (pre ++ lY c d sb ++ post)
      (realRank pre) (pairParity (chiB d sb) c) (sigma0 (chiB d sb) c) μ₀)
    (hQ2 : IsBlockFrobData n (pre ++ lY c d sb ++ post) (pre ++ lZ c d sb ++ post)
      (realRank pre + 1) (pairParity (chiA d sb) c) (sigma0 (chiA d sb) c) μ₁)
    (hD : IsBlockFrobData n (pre ++ lX c d sb ++ post) (pre ++ lV c d sb ++ post)
      (realRank pre + 1) (pairParity (chiB d sb) (chiA d sb))
      ((-1) ^ (chiA d sb).parity.val)
      (tailMultiplier d.weight.natAbs (pairParity (chiB d sb) (chiA d sb))
        ((-1) ^ (chiA d sb).parity.val)))
    (hT : IsBlockFrobData n (pre ++ lZ c d sb ++ post) (pre ++ lW c d sb ++ post)
      (realRank pre) (pairParity (chiB d sb) (chiA d sb))
      ((-1) ^ (chiA d sb).parity.val)
      (tailMultiplier d.weight.natAbs (pairParity (chiB d sb) (chiA d sb))
        ((-1) ^ (chiA d sb).parity.val)))
    (_hμ₀ : IsRecurrent (c.exponent - (chiB d sb).exponent + 1)
      (pairParity (chiB d sb) c) μ₀)
    (_hμ₁ : IsRecurrent (c.exponent - (chiA d sb).exponent + 1)
      (pairParity (chiA d sb) c) μ₁)
    (z : KF n (pre ++ lX c d sb ++ post)) (_hz : blockFrobMap hD z = 0),
    blockFrobMap hT (blockFrobMap hQ2 (blockFrobMap hQ1 z)) = 0

/-- The reverse statement follows from the reflected high-mode argument and compact slices. -/
theorem realTailKernelReverse : RealTailKernelReverseStatement := by
  intro n c d sb pre post hn hl μ₀ μ₁ hQ1 hQ2 hD hT hμ₀ hμ₁ z hz
  exact kernel_step_inStages c d sb pre post hn hl hQ1 hQ2 hD hT hμ₀ hμ₁ z hz

end Langlands.Archimedean

import Langlands.Representation.Archimedean.RealInducedCharacterMaps
import Langlands.Representation.Archimedean.RealExponentDeformation

/-!
# Injection into the reverse of a real character pair

For either compatible choice of signs, a nonzero real discrete-series induction
block embeds into the high/low character pair. The two maps from the low/high
pair have the same Fourier kernel, and the tail map to the induction block is
surjective.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean.RealDiscreteSplitInjection

open Langlands.LocalFactor.Archimedean
open RealBlockFrobeniusMap RealBlockJacquet RealBlockMultiplier RealCharacterPair
  RealCharacterPairReducible RealInducedCharacter RealStandardFiltration

attribute [local instance 100] LieRing.ofAssociativeRing

set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {pre post : List RealBlock} {d : ComplexCharacterData} {sa sb : Fin 2}

private theorem sigma0_sq (c b : RealCharacterData) : sigma0 c b ^ 2 = 1 := by
  rw [sigma0_eq, mul_pow, neg_one_pow_sq_fin, neg_one_pow_sq_fin, one_mul]

private theorem data_reverse
    (hn : realRank (pre ++ [RealBlock.induced d] ++ post) = n)
    (hl : 0 < d.weight.natAbs) (hs : (sa.val + sb.val) % 2 = (d.weight.natAbs + 1) % 2) :
    IsBlockFrobData n (pre ++ cd (cb d sb) (ca d sa) ++ post)
      (pre ++ dc (cb d sb) (ca d sa) ++ post) (realRank pre)
      (pairParity (cb d sb) (ca d sa)) (sigma0 (cb d sb) (ca d sa))
      (tailMultiplier d.weight.natAbs (pairParity (cb d sb) (ca d sa))
        (sigma0 (cb d sb) (ca d sa))) := by
  have hn' : realRank (pre ++ RealBlock.character (cb d sb) ::
      RealBlock.character (ca d sa) :: post) = n := by
    rw [← mid_pair]
    exact realRank_tail_mid hn
  have hsym := (isSymmetric_tailMultiplier hl (pairParity_eq (cb d sb) (ca d sa))
    (tail_parity hs) (sigma0_sq (cb d sb) (ca d sa))).inv
  rw [sigma0_inv] at hsym
  rw [mid_pair]
  simpa only [sigma0_inv, inv_inv] using data_unswap hn' hsym

private theorem reverse_exact
    (hn : realRank (pre ++ [RealBlock.induced d] ++ post) = n)
    (hl : 0 < d.weight.natAbs) (hs : (sa.val + sb.val) % 2 = (d.weight.natAbs + 1) % 2) :
    IsRealIntertwinerModulo n (pre ++ cd (cb d sb) (ca d sa) ++ post)
      (pre ++ dc (cb d sb) (ca d sa) ++ post) ⊥ (blockFrobMap (data_reverse hn hl hs)) := by
  refine isRealIntertwinerModulo_blockFrobMap _ ?_ _
  rw [exponent_mid_zero pre post (by rw [realRank_cd]; norm_num),
    exponent_mid_one pre post (by rw [realRank_cd]; norm_num)]
  show IsRecurrent (bExp d - aExp d + 1) _ _
  rw [show bExp d - aExp d + 1 = 1 - (d.weight.natAbs : ℂ) by
    linear_combination -(aExp_sub_bExp d)]
  exact isRecurrent_tailMultiplier hl (pairParity_eq _ _) (tail_parity hs) (sigma0_sq _ _)

private theorem blockFrobMap_eq_zero_iff {xs ys : List RealBlock} {p : ℕ} {ε : ℤ} {σ : ℂ}
    {μ : ℤ → ℂ} (h : IsBlockFrobData n xs ys p ε σ μ) (f : KF n xs) :
    blockFrobMap h f = 0 ↔ ∀ j : ℤ, Even (j - ε) → μ j ≠ 0 →
      ∀ k ∈ unitaryCompact ℝ n, blockFourierCoefficient n p j f k = 0 := by
  constructor
  · intro hf j _ hj k hk
    have hcoef := blockFourierCoefficient_blockFrobMap h f hk j
    rw [hf, ZeroMemClass.coe_zero, blockFourierCoefficient_zero] at hcoef
    exact (mul_eq_zero.mp hcoef.symm).resolve_left hj
  · intro hf
    refine eq_of_blockFourierCoefficient_eq h.lt fun j k hk => ?_
    rw [blockFourierCoefficient_blockFrobMap h f hk, ZeroMemClass.coe_zero,
      blockFourierCoefficient_zero]
    by_cases hj : Even (j - ε)
    · by_cases hμ : μ j = 0
      · rw [hμ, zero_mul]
      · rw [hf j hj hμ k hk, mul_zero]
    · rw [blockFourierCoefficient_eq_zero_of_not_even h.lt h.par f hj k, mul_zero]

/-- The map from the discrete-series block into the high/low character pair, obtained by
composing the tail section with the map to the reversed pair. -/
def splitInjection (hn : realRank (pre ++ [RealBlock.induced d] ++ post) = n)
    (hl : 0 < d.weight.natAbs) (hs : (sa.val + sb.val) % 2 = (d.weight.natAbs + 1) % 2) :
    KF n (pre ++ [RealBlock.induced d] ++ post) →ₗ[ℂ]
      KF n (pre ++ dc (cb d sb) (ca d sa) ++ post) :=
  blockFrobMap (data_reverse hn hl hs) ∘ₗ blockFrobMap (data_tailInv hn hl hs)

theorem splitInjection_injective_and_intertwines
    (hn : realRank (pre ++ [RealBlock.induced d] ++ post) = n)
    (hl : 0 < d.weight.natAbs) (hs : (sa.val + sb.val) % 2 = (d.weight.natAbs + 1) % 2) :
    Function.Injective (splitInjection hn hl hs) ∧
      IsRealStandardIntertwiner n (realStandardRep n (pre ++ dc (cb d sb) (ca d sa) ++ post))
        (realStandardLie n (pre ++ dc (cb d sb) (ca d sa) ++ post))
        (pre ++ [RealBlock.induced d] ++ post) (splitInjection hn hl hs) := by
  let Q := blockFrobMap (data_tail hn hl hs)
  let S := blockFrobMap (data_tailInv hn hl hs)
  let T := blockFrobMap (data_reverse hn hl hs)
  have hsection : ∀ f, Q (S f) = f := tail_tailInv hn hl hs
  have hker : ∀ f, T f = 0 ↔ Q f = 0 := by
    intro f
    change blockFrobMap (data_reverse hn hl hs) f = 0 ↔ blockFrobMap (data_tail hn hl hs) f = 0
    rw [blockFrobMap_eq_zero_iff, blockFrobMap_eq_zero_iff]
    have hsupport (j : ℤ) (hj : Even (j - pairParity (cb d sb) (ca d sa))) :=
      (tailMultiplier_ne_zero_iff hl (pairParity_eq _ _) (tail_parity hs)
        (sigma0_sq (cb d sb) (ca d sa)) hj).trans
        (tailMultiplier_ne_zero_iff hl (pairParity_eq _ _) (tail_parity hs)
          (neg_one_pow_sq_fin sa) hj).symm
    constructor <;> intro hf j hj hnonzero k hk
    · exact hf j hj ((hsupport j hj).2 hnonzero) k hk
    · exact hf j hj ((hsupport j hj).1 hnonzero) k hk
  have hfactor : splitInjection hn hl hs ∘ₗ Q = T := by
    apply LinearMap.ext
    intro f
    change T (S (Q f)) = T f
    have hz := (hker (S (Q f) - f)).2 (by rw [map_sub, hsection, sub_self])
    rwa [map_sub, sub_eq_zero] at hz
  refine ⟨(injective_iff_map_eq_zero _).2 fun f hf => ?_,
    RealExponentDeformation.isRealStandardIntertwiner_of_modulo_bot
      (modulo_of_comp_surjective (reverse_exact hn hl hs) (modulo_tail hn hl hs)
        (tail_surjective hn hl hs) hfactor)⟩
  change T (S f) = 0 at hf
  exact (hsection f).symm.trans ((hker (S f)).1 hf)

end Langlands.Archimedean.RealDiscreteSplitInjection

import Langlands.Representation.Archimedean.RealInductionStagesSlice
import Langlands.Representation.Archimedean.RealCharacterInducedPushforward
import Langlands.Representation.Archimedean.RealSwapLandingIntegral
import Langlands.Representation.Archimedean.RealSwapLandingMirror

/-! # Tail-kernel compatibility in surrounding blocks -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

namespace RealTailKernelInStages

open InductionStages RealBlockFrobeniusMap RealBlockMultiplier RealCharacterPair
open RealCharacterInducedPushforward RealCharacterPairReducible RealStandardFiltration

section Slices

variable {n a r p : ℕ} {pre ds es post : List RealBlock} {ε : ℤ} {σ : ℂ}
  {μ : ℤ → ℂ}

/-- The actual Frobenius map commutes with each compact slice when the local and ambient
data have the same multiplier. -/
theorem frob_slice (h : a + r ≤ n) (ha : realRank pre = a)
    (hd : realRank ds = r) (he : realRank es = r)
    (hA : IsBlockFrobData n (pre ++ ds ++ post) (pre ++ es ++ post) (a + p) ε σ μ)
    (hL : IsBlockFrobData r ds es p ε σ μ)
    (κ : unitaryCompact ℝ n) (F : KF n (pre ++ ds ++ post)) :
    sliceK h ha he κ (blockFrobMap hA F) =
      blockFrobMap hL (sliceK h ha hd κ F) := by
  refine eq_of_blockFourierCoefficient_eq hL.lt fun j g hg => ?_
  change blockFourierCoefficient r p j
      (slice h (κ : Langlands.GeneralLinear n ℝ)
        (blockFrobMap hA F : Langlands.GeneralLinear n ℝ → ℂ)) g = _
  rw [blockFourierCoefficient_blockFrobMap hL _ hg]
  change _ = μ j * blockFourierCoefficient r p j
    (slice h (κ : Langlands.GeneralLinear n ℝ) (F : Langlands.GeneralLinear n ℝ → ℂ)) g
  rw [blockFourierCoefficient_slice h hL.lt, blockFourierCoefficient_slice h hL.lt,
    blockFourierCoefficient_blockFrobMap hA F
      ((unitaryCompact ℝ n).mul_mem (blockEmb_mem_unitaryCompact h hg) κ.2)]
  ring

/-- Compact slices detect the zero vector. No ambient total-rank hypothesis is needed. -/
theorem eq_zero_of_slices (h : a + r ≤ n) (ha : realRank pre = a)
    (hd : realRank ds = r) (F : KF n (pre ++ ds ++ post))
    (hF : ∀ κ, sliceK h ha hd κ F = 0) : F = 0 := by
  apply Subtype.ext
  refine eq_of_eqOn_unitaryCompact_of_mem_principalSeries F.2.1.1
    (0 : KF n (pre ++ ds ++ post)).2.1.1 fun κ hκ => ?_
  have hz := congrArg (fun v : KF r ds => (v : Langlands.GeneralLinear r ℝ → ℂ) 1)
    (hF ⟨κ, hκ⟩)
  simpa only [sliceK_apply_one, ZeroMemClass.coe_zero, Pi.zero_apply] using hz

end Slices

section Kernel

variable {n : ℕ} (pre post : List RealBlock) (c : RealCharacterData)
  (d : ComplexCharacterData) (sb : Fin 2)

/-- Two consecutive exact swaps preserve the kernel of the tail on an ascending pair,
with arbitrary surrounding blocks. All four operators are actual ambient Frobenius maps. -/
theorem kernel_step (hn : realRank pre + 3 + realRank post = n)
    (hl : 0 < d.weight.natAbs) {μ₀ μ₁ : ℤ → ℂ}
    (hQ1 : IsBlockFrobData n (pre ++ lY c d sb ++ post) (pre ++ lX c d sb ++ post)
      (realRank pre) (pairParity c (chiB d sb)) (sigma0 c (chiB d sb)) μ₀)
    (hQ2 : IsBlockFrobData n (pre ++ lZ c d sb ++ post) (pre ++ lY c d sb ++ post)
      (realRank pre + 1) (pairParity c (chiA d sb)) (sigma0 c (chiA d sb)) μ₁)
    (hT : IsBlockFrobData n (pre ++ lZ c d sb ++ post) (pre ++ lW c d sb ++ post)
      (realRank pre) (pairParity (chiB d sb) (chiA d sb)) ((-1) ^ (chiA d sb).parity.val)
      (tailMultiplier d.weight.natAbs (pairParity (chiB d sb) (chiA d sb))
        ((-1) ^ (chiA d sb).parity.val)))
    (hD : IsBlockFrobData n (pre ++ lX c d sb ++ post) (pre ++ lV c d sb ++ post)
      (realRank pre + 1) (pairParity (chiB d sb) (chiA d sb))
      ((-1) ^ (chiA d sb).parity.val)
      (tailMultiplier d.weight.natAbs (pairParity (chiB d sb) (chiA d sb))
        ((-1) ^ (chiA d sb).parity.val)))
    (hμ₀ : IsRecurrent ((chiB d sb).exponent - c.exponent + 1)
      (pairParity c (chiB d sb)) μ₀)
    (hμ₁ : IsRecurrent ((chiA d sb).exponent - c.exponent + 1)
      (pairParity c (chiA d sb)) μ₁)
    (z : KF n (pre ++ lZ c d sb ++ post)) (hz : blockFrobMap hT z = 0) :
    blockFrobMap hD (blockFrobMap hQ1 (blockFrobMap hQ2 z)) = 0 := by
  have h : realRank pre + 3 ≤ n := by omega
  have hrX : realRank (lX c d sb) = 3 := rfl
  have hrY : realRank (lY c d sb) = 3 := rfl
  have hrZ : realRank (lZ c d sb) = 3 := rfl
  have hrV : realRank (lV c d sb) = 3 := rfl
  have hrW : realRank (lW c d sb) = 3 := rfl
  have hQ1' := dataQ1 c d sb hQ1.sym
  have hQ2' := dataQ2 c d sb hQ2.sym
  apply eq_zero_of_slices h rfl hrV
  intro κ
  rw [frob_slice h rfl hrX hrV hD (dataD1 c d sb hl),
    frob_slice h rfl hrY hrX (by simpa only [Nat.add_zero] using hQ1) hQ1',
    frob_slice h rfl hrZ hrY hQ2 hQ2']
  apply RealCharacterInducedPushforward.kernel_step c d sb
    (RealSwapLandingMirror.characterFirst_of_inducedFirst RealSwapLandingIntegral.inducedFirst)
    hl hQ1' hQ2' hμ₀ hμ₁
  rw [← frob_slice h rfl hrZ hrW
    (by simpa only [Nat.add_zero] using hT) (dataT0 c d sb hl), hz, map_zero]

end Kernel

end RealTailKernelInStages

open RealTailKernelInStages RealCharacterInducedPushforward RealCharacterPairReducible
open RealBlockFrobeniusMap RealBlockMultiplier RealCharacterPair RealStandardFiltration

/-- Two exact recurrent swaps preserve an ascending induction tail kernel in arbitrary
surrounding blocks. The four map data remain explicit. -/
def RealTailKernelInStagesStatement : Prop :=
  ∀ {n : ℕ} (pre post : List RealBlock) (c : RealCharacterData)
    (d : ComplexCharacterData) (sb : Fin 2)
    (_hn : realRank pre + 3 + realRank post = n)
    (_hl : 0 < d.weight.natAbs) {μ₀ μ₁ : ℤ → ℂ}
    (hQ1 : IsBlockFrobData n (pre ++ lY c d sb ++ post) (pre ++ lX c d sb ++ post)
      (realRank pre) (pairParity c (chiB d sb)) (sigma0 c (chiB d sb)) μ₀)
    (hQ2 : IsBlockFrobData n (pre ++ lZ c d sb ++ post) (pre ++ lY c d sb ++ post)
      (realRank pre + 1) (pairParity c (chiA d sb)) (sigma0 c (chiA d sb)) μ₁)
    (hT : IsBlockFrobData n (pre ++ lZ c d sb ++ post) (pre ++ lW c d sb ++ post)
      (realRank pre) (pairParity (chiB d sb) (chiA d sb)) ((-1) ^ (chiA d sb).parity.val)
      (tailMultiplier d.weight.natAbs (pairParity (chiB d sb) (chiA d sb))
        ((-1) ^ (chiA d sb).parity.val)))
    (hD : IsBlockFrobData n (pre ++ lX c d sb ++ post) (pre ++ lV c d sb ++ post)
      (realRank pre + 1) (pairParity (chiB d sb) (chiA d sb))
      ((-1) ^ (chiA d sb).parity.val)
      (tailMultiplier d.weight.natAbs (pairParity (chiB d sb) (chiA d sb))
        ((-1) ^ (chiA d sb).parity.val)))
    (_hμ₀ : IsRecurrent ((chiB d sb).exponent - c.exponent + 1)
      (pairParity c (chiB d sb)) μ₀)
    (_hμ₁ : IsRecurrent ((chiA d sb).exponent - c.exponent + 1)
      (pairParity c (chiA d sb)) μ₁)
    (z : KF n (pre ++ lZ c d sb ++ post)) (_hz : blockFrobMap hT z = 0),
    blockFrobMap hD (blockFrobMap hQ1 (blockFrobMap hQ2 z)) = 0

/-- The ambient tail-kernel statement follows from the proved compact slice compatibility. -/
theorem realTailKernelInStages : RealTailKernelInStagesStatement := by
  intro n pre post c d sb hn hl μ₀ μ₁ hQ1 hQ2 hT hD hμ₀ hμ₁ z hz
  exact RealTailKernelInStages.kernel_step pre post c d sb hn hl hQ1 hQ2 hT hD hμ₀ hμ₁ z hz

end Langlands.Archimedean

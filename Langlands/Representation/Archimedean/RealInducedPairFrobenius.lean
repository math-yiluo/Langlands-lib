import Langlands.Representation.Archimedean.RealSwapLandingInStages
import Langlands.Representation.Archimedean.RealBlockFrobeniusDisjoint

/-!
# Four character crossings between two induction blocks

All Frobenius maps have full-character targets. The Fourier conditions for the two
induction blocks are recovered separately by the two orders of the middle crossings.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

namespace RealInducedPairFrobenius

open RealJacquetFrobenius RealBlockPosition RealBlockFrobeniusMap RealBlockMultiplier
open RealBlockFourierFinite RealSwapLandingMirror

set_option backward.isDefEq.respectTransparency false

abbrev KF (ds : List RealBlock) :=
  kFiniteFunctions (realStandardModule 4 ds) (unitaryCompact ℝ 4)

/-- The first actual position character of an induction block. -/
def first (d : ComplexCharacterData) : RealCharacterData :=
  charData ⟨(d.weight.natAbs + 1) % 2, Nat.mod_lt _ two_pos⟩
    (d.exponent + (d.weight.natAbs : ℂ) / 2)

/-- The second actual position character of an induction block. -/
def second (d : ComplexCharacterData) : RealCharacterData :=
  charData 0 (d.exponent - (d.weight.natAbs : ℂ) / 2)

abbrev src (d e : ComplexCharacterData) : List RealBlock := [.induced d, .induced e]
abbrev dst (d e : ComplexCharacterData) : List RealBlock := [.induced e, .induced d]
abbrev l0 (d e : ComplexCharacterData) : List RealBlock :=
  [.character (first d), .character (second d), .character (first e), .character (second e)]
abbrev l1 (d e : ComplexCharacterData) : List RealBlock :=
  [.character (first d), .character (first e), .character (second d), .character (second e)]
abbrev l10 (d e : ComplexCharacterData) : List RealBlock :=
  [.character (first e), .character (first d), .character (second d), .character (second e)]
abbrev l12 (d e : ComplexCharacterData) : List RealBlock :=
  [.character (first d), .character (first e), .character (second e), .character (second d)]
abbrev l3 (d e : ComplexCharacterData) : List RealBlock :=
  [.character (first e), .character (first d), .character (second e), .character (second d)]
abbrev l4 (d e : ComplexCharacterData) : List RealBlock :=
  [.character (first e), .character (second e), .character (first d), .character (second d)]

/-- Forget the second induction constraint. -/
abbrev sD (d e : ComplexCharacterData) : List RealBlock :=
  [.induced d, .character (first e), .character (second e)]

/-- Forget the first induction constraint. -/
abbrev sE (d e : ComplexCharacterData) : List RealBlock :=
  [.character (first d), .character (second d), .induced e]

/-- Partial target of the first induced-first landing. -/
abbrev tD (d e : ComplexCharacterData) : List RealBlock :=
  [.character (first e), .induced d, .character (second e)]

/-- Partial target of the first character-first landing. -/
abbrev tE (d e : ComplexCharacterData) : List RealBlock :=
  [.character (first d), .induced e, .character (second d)]

theorem posChar_l0 (d e : ComplexCharacterData) :
    realPositionCharacter (l0 d e) = realPositionCharacter (src d e) := by
  funext i x
  rw [realPositionCharacter_eq_charFun, realPositionCharacter_eq_charFun]
  rcases i with _ | _ | _ | _ | i <;> rfl

theorem posChar_sD (d e : ComplexCharacterData) :
    realPositionCharacter (sD d e) = realPositionCharacter (src d e) := by
  funext i x
  rw [realPositionCharacter_eq_charFun, realPositionCharacter_eq_charFun]
  rcases i with _ | _ | _ | _ | i <;> rfl

theorem posChar_sE (d e : ComplexCharacterData) :
    realPositionCharacter (sE d e) = realPositionCharacter (src d e) := by
  funext i x
  rw [realPositionCharacter_eq_charFun, realPositionCharacter_eq_charFun]
  rcases i with _ | _ | _ | _ | i <;> rfl

theorem posChar_tD (d e : ComplexCharacterData) :
    realPositionCharacter (tD d e) = realPositionCharacter (l10 d e) := by
  funext i x
  rw [realPositionCharacter_eq_charFun, realPositionCharacter_eq_charFun]
  rcases i with _ | _ | _ | _ | i <;> rfl

theorem posChar_tE (d e : ComplexCharacterData) :
    realPositionCharacter (tE d e) = realPositionCharacter (l12 d e) := by
  funext i x
  rw [realPositionCharacter_eq_charFun, realPositionCharacter_eq_charFun]
  rcases i with _ | _ | _ | _ | i <;> rfl

theorem posChar_dst (d e : ComplexCharacterData) :
    realPositionCharacter (dst d e) = realPositionCharacter (l4 d e) :=
  (posChar_l0 e d).symm

/-- Forgetting Fourier constraints preserves compact finiteness. -/
theorem kf_le {ds es : List RealBlock}
    (hc : realPositionCharacter es = realPositionCharacter ds)
    (hi : ∀ p x, realInducedBlockAt es p = some x → realInducedBlockAt ds p = some x) :
    KF ds ≤ KF es := by
  intro f hf
  refine ⟨⟨?_, fun p x hx k hk g => hf.1.2 p x (hi p x hx) k hk g⟩, hf.2⟩
  rw [hc]
  exact hf.1.1

theorem src_le_l0 (d e : ComplexCharacterData) : KF (src d e) ≤ KF (l0 d e) := by
  refine kf_le (posChar_l0 d e) ?_
  intro p x hx
  rcases p with _ | _ | _ | _ | p <;> simp [realInducedBlockAt] at hx

theorem src_le_sD (d e : ComplexCharacterData) : KF (src d e) ≤ KF (sD d e) := by
  refine kf_le (posChar_sD d e) ?_
  intro p x hx
  rcases p with _ | _ | _ | _ | p <;> simp [realInducedBlockAt] at hx ⊢
  exact hx

theorem src_le_sE (d e : ComplexCharacterData) : KF (src d e) ≤ KF (sE d e) := by
  refine kf_le (posChar_sE d e) ?_
  intro p x hx
  rcases p with _ | _ | _ | _ | p <;> simp [realInducedBlockAt] at hx ⊢
  exact hx

/-- Recover the middle induction constraint from its compact forbidden modes. -/
theorem mem_tD {d e : ComplexCharacterData} (f : KF (l10 d e))
    (hK : ∀ g ∈ unitaryCompact ℝ 4, ∀ k : ℤ, |k| < |d.weight| →
      blockFourierCoefficient 4 1 k (f : Langlands.GeneralLinear 4 ℝ → ℂ) g = 0) :
    (f : Langlands.GeneralLinear 4 ℝ → ℂ) ∈ KF (tD d e) := by
  refine ⟨mem_realStandardModule_of_unitaryCompact (N := 4) (ds := tD d e) rfl ?_ ?_, f.2.2⟩
  · rw [posChar_tD]
    exact f.2.1.1
  · intro p x hx k hk g hg
    rcases p with _ | _ | _ | _ | p <;> simp [realInducedBlockAt] at hx
    subst x
    exact hK g hg k hk

theorem mem_tE {d e : ComplexCharacterData} (f : KF (l12 d e))
    (hK : ∀ g ∈ unitaryCompact ℝ 4, ∀ k : ℤ, |k| < |e.weight| →
      blockFourierCoefficient 4 1 k (f : Langlands.GeneralLinear 4 ℝ → ℂ) g = 0) :
    (f : Langlands.GeneralLinear 4 ℝ → ℂ) ∈ KF (tE d e) := by
  refine ⟨mem_realStandardModule_of_unitaryCompact (N := 4) (ds := tE d e) rfl ?_ ?_, f.2.2⟩
  · rw [posChar_tE]
    exact f.2.1.1
  · intro p x hx k hk g hg
    rcases p with _ | _ | _ | _ | p <;> simp [realInducedBlockAt] at hx
    subst x
    exact hK g hg k hk

/-- Recover both induction constraints from their compact forbidden modes. -/
theorem mem_dst {d e : ComplexCharacterData} (f : KF (l4 d e))
    (hd : ∀ g ∈ unitaryCompact ℝ 4, ∀ k : ℤ, |k| < |d.weight| →
      blockFourierCoefficient 4 2 k (f : Langlands.GeneralLinear 4 ℝ → ℂ) g = 0)
    (he : ∀ g ∈ unitaryCompact ℝ 4, ∀ k : ℤ, |k| < |e.weight| →
      blockFourierCoefficient 4 0 k (f : Langlands.GeneralLinear 4 ℝ → ℂ) g = 0) :
    (f : Langlands.GeneralLinear 4 ℝ → ℂ) ∈ KF (dst d e) := by
  refine ⟨mem_realStandardModule_of_unitaryCompact (N := 4) (ds := dst d e) rfl ?_ ?_, f.2.2⟩
  · rw [posChar_dst]
    exact f.2.1.1
  · intro p x hx k hk g hg
    rcases p with _ | _ | _ | _ | p <;> simp [realInducedBlockAt] at hx
    · subst x
      exact he g hg k hk
    · subst x
      exact hd g hg k hk

/-- Swap two adjacent character blocks for any representative of their parity class. -/
theorem characterSwapData {n : ℕ} {pre post : List RealBlock} {c b : RealCharacterData}
    {ε : ℕ} {μ : ℤ → ℂ}
    (hn : realRank (pre ++ [.character b, .character c] ++ post) = n)
    (hε : ε % 2 = (c.parity.val + b.parity.val) % 2)
    (hs : IsSymmetric (ε : ℤ) ((-1 : ℂ) ^ ε) μ) :
    IsBlockFrobData n (pre ++ [.character c, .character b] ++ post)
      (pre ++ [.character b, .character c] ++ post) (realRank pre) (ε : ℤ)
      ((-1 : ℂ) ^ ε) μ := by
  have hsg : (-1 : ℂ) ^ ε = (-1) ^ c.parity.val * (-1) ^ b.parity.val := by
    rw [← pow_add]
    exact neg_one_pow_congr hε
  refine IsBlockFrobData.of_mid hn rfl rfl rfl rfl ?_ hs ?_ ?_ ?_
  · simp only [realPositionCharacter_neg_one, realPositionSign, zpow_natCast]
    exact hsg
  · simp only [realPositionCharacter_neg_one, realPositionSign]
    rw [hsg]
    have hc : ((-1 : ℂ) ^ c.parity.val) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm _ 2, pow_mul, neg_one_sq, one_pow]
    linear_combination -(-1 : ℂ) ^ b.parity.val * hc
  · simp only [realPositionCharacter_neg_one, realPositionSign]
    rw [hsg]
    have hb : ((-1 : ℂ) ^ b.parity.val) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm _ 2, pow_mul, neg_one_sq, one_pow]
    linear_combination -(-1 : ℂ) ^ c.parity.val * hb
  · intro f hf
    simp [realInducedBlockAt] at hf

/-- The four recurrence parameters and parity classes for the exchange word. -/
structure MultiplierData (d e : ComplexCharacterData) (δ : ℂ)
    (μ₁ μ₀ μ₂ μ₃ : ℤ → ℂ) : Prop where
  rec1 : IsRecurrent δ ((e.weight.natAbs + 1 : ℕ) : ℤ) μ₁
  sym1 : IsSymmetric ((e.weight.natAbs + 1 : ℕ) : ℤ)
    ((-1 : ℂ) ^ (e.weight.natAbs + 1)) μ₁
  rec0 : IsRecurrent (δ + (d.weight.natAbs : ℂ))
    ((d.weight.natAbs + e.weight.natAbs + 2 : ℕ) : ℤ) μ₀
  sym0 : IsSymmetric ((d.weight.natAbs + e.weight.natAbs + 2 : ℕ) : ℤ)
    ((-1 : ℂ) ^ (d.weight.natAbs + e.weight.natAbs + 2)) μ₀
  rec2 : IsRecurrent (δ + (e.weight.natAbs : ℂ)) 0 μ₂
  sym2 : IsSymmetric 0 1 μ₂
  rec3 : IsRecurrent (δ + (d.weight.natAbs : ℂ) + (e.weight.natAbs : ℂ))
    ((d.weight.natAbs + 1 : ℕ) : ℤ) μ₃
  sym3 : IsSymmetric ((d.weight.natAbs + 1 : ℕ) : ℤ)
    ((-1 : ℂ) ^ (d.weight.natAbs + 1)) μ₃

namespace MultiplierData

variable {d e : ComplexCharacterData} {δ : ℂ} {μ₁ μ₀ μ₂ μ₃ : ℤ → ℂ}
    (h : MultiplierData d e δ μ₁ μ₀ μ₂ μ₃)

include h

/-- First crossing, at position one. -/
theorem data1 : IsBlockFrobData 4 (l0 d e) (l1 d e) 1
    ((e.weight.natAbs + 1 : ℕ) : ℤ) ((-1 : ℂ) ^ (e.weight.natAbs + 1)) μ₁ := by
  exact characterSwapData (pre := [.character (first d)]) (post := [.character (second e)])
    (c := second d) (b := first e) rfl (by simp [first, second, charData]) h.sym1

/-- Left middle crossing. -/
theorem data0 : IsBlockFrobData 4 (l1 d e) (l10 d e) 0
    ((d.weight.natAbs + e.weight.natAbs + 2 : ℕ) : ℤ)
    ((-1 : ℂ) ^ (d.weight.natAbs + e.weight.natAbs + 2)) μ₀ := by
  exact characterSwapData (pre := [])
    (post := [.character (second d), .character (second e)])
    (c := first d) (b := first e) rfl
    (by dsimp [first, charData]; omega) h.sym0

/-- Right middle crossing in the alternative order. -/
theorem data2 : IsBlockFrobData 4 (l1 d e) (l12 d e) 2 0 1 μ₂ := by
  exact characterSwapData (pre := [.character (first d), .character (first e)]) (post := [])
    (c := second d) (b := second e) (ε := 0) rfl rfl h.sym2

/-- Right middle crossing after the left middle crossing. -/
theorem data20 : IsBlockFrobData 4 (l10 d e) (l3 d e) 2 0 1 μ₂ := by
  exact characterSwapData (pre := [.character (first e), .character (first d)]) (post := [])
    (c := second d) (b := second e) (ε := 0) rfl rfl h.sym2

/-- Left middle crossing after the right middle crossing. -/
theorem data02 : IsBlockFrobData 4 (l12 d e) (l3 d e) 0
    ((d.weight.natAbs + e.weight.natAbs + 2 : ℕ) : ℤ)
    ((-1 : ℂ) ^ (d.weight.natAbs + e.weight.natAbs + 2)) μ₀ := by
  exact characterSwapData (pre := [])
    (post := [.character (second e), .character (second d)])
    (c := first d) (b := first e) rfl
    (by dsimp [first, charData]; omega) h.sym0

/-- Last crossing, at position one, with a full-character target. -/
theorem data3 : IsBlockFrobData 4 (l3 d e) (l4 d e) 1
    ((d.weight.natAbs + 1 : ℕ) : ℤ) ((-1 : ℂ) ^ (d.weight.natAbs + 1)) μ₃ := by
  exact characterSwapData (pre := [.character (first e)]) (post := [.character (second d)])
    (c := first d) (b := second e) rfl (by simp [first, second, charData]) h.sym3

/-- First crossing after forgetting both induction constraints. -/
def to1 : KF (src d e) →ₗ[ℂ] KF (l1 d e) :=
  (blockFrobMap h.data1).comp (Submodule.inclusion (src_le_l0 d e))

/-- First two crossings in the induced-first order. -/
def to10 : KF (src d e) →ₗ[ℂ] KF (l10 d e) :=
  (blockFrobMap h.data0).comp h.to1

/-- First two crossings in the character-first order. -/
def to12 : KF (src d e) →ₗ[ℂ] KF (l12 d e) :=
  (blockFrobMap h.data2).comp h.to1

/-- First three crossings in the induced-first order. -/
def to3 : KF (src d e) →ₗ[ℂ] KF (l3 d e) :=
  (blockFrobMap h.data20).comp h.to10

/-- The complete four-crossing map with a full-character target. -/
def to4 : KF (src d e) →ₗ[ℂ] KF (l4 d e) :=
  (blockFrobMap h.data3).comp h.to3

/-- The two orders of the middle crossings give the same function. -/
theorem to3_eq (f : KF (src d e)) :
    h.to3 f = blockFrobMap h.data02 (h.to12 f) :=
  RealBlockFrobeniusDisjoint.blockFrobMap_disjoint_comm
    h.data0 h.data20 h.data2 h.data02 (Or.inl (by decide)) (h.to1 f)

/-- The first induced-first GL3 move recovers the d-block in the middle. -/
theorem landing10 (f : KF (src d e)) :
    (h.to10 f : Langlands.GeneralLinear 4 ℝ → ℂ) ∈ KF (tD d e) := by
  apply mem_tD
  apply RealSwapLandingInStages.realSwapLandingInStages.1 4 [] [.character (second e)]
    (first e) d δ μ₀ μ₁ (f : Langlands.GeneralLinear 4 ℝ → ℂ)
    (h.to1 f : Langlands.GeneralLinear 4 ℝ → ℂ)
    (h.to10 f : Langlands.GeneralLinear 4 ℝ → ℂ) rfl
  · exact isRecurrent_congr h.rec1 (by dsimp [first, charData]; exact even_sub_mod _)
  · exact isSymmetric_congr h.sym1 (by dsimp [first, charData]; exact even_sub_mod _)
      (neg_one_pow_congr (by dsimp [first, charData]; omega))
  · exact isRecurrent_congr h.rec0 (by dsimp [first, charData]; rw [Int.even_iff]; omega)
  · exact isSymmetric_congr h.sym0 (by dsimp [first, charData]; rw [Int.even_iff]; omega)
      (neg_one_pow_congr (by dsimp [first, charData]; omega))
  · exact src_le_sD d e f.2
  · exact RealBlockJacquet.continuous_coe _
  · exact RealBlockJacquet.continuous_coe _
  · intro g hg k
    exact blockFourierCoefficient_blockFrobMap h.data1 _ hg k
  · intro g hg k
    exact blockFourierCoefficient_blockFrobMap h.data0 _ hg k

/-- The first character-first GL3 move recovers the e-block in the middle. -/
theorem landing12 (f : KF (src d e)) :
    (h.to12 f : Langlands.GeneralLinear 4 ℝ → ℂ) ∈ KF (tE d e) := by
  apply mem_tE
  apply RealSwapLandingInStages.realSwapLandingInStages.2 4 [.character (first d)] []
    (second d) e δ μ₁ μ₂ (f : Langlands.GeneralLinear 4 ℝ → ℂ)
    (h.to1 f : Langlands.GeneralLinear 4 ℝ → ℂ)
    (h.to12 f : Langlands.GeneralLinear 4 ℝ → ℂ) rfl
  · exact h.rec1
  · exact h.sym1
  · exact h.rec2
  · exact h.sym2
  · exact src_le_sE d e f.2
  · exact RealBlockJacquet.continuous_coe _
  · exact RealBlockJacquet.continuous_coe _
  · intro g hg k
    exact blockFourierCoefficient_blockFrobMap h.data1 _ hg k
  · intro g hg k
    exact blockFourierCoefficient_blockFrobMap h.data2 _ hg k

/-- The induced-first route establishes the final d-block Fourier condition. -/
theorem landing4_d (f : KF (src d e)) :
    ∀ g ∈ unitaryCompact ℝ 4, ∀ k : ℤ, |k| < |d.weight| →
      blockFourierCoefficient 4 2 k (h.to4 f : Langlands.GeneralLinear 4 ℝ → ℂ) g = 0 := by
  apply RealSwapLandingInStages.realSwapLandingInStages.1 4 [.character (first e)] []
    (second e) d (δ + (e.weight.natAbs : ℂ)) μ₃ μ₂
    (h.to10 f : Langlands.GeneralLinear 4 ℝ → ℂ)
    (h.to3 f : Langlands.GeneralLinear 4 ℝ → ℂ)
    (h.to4 f : Langlands.GeneralLinear 4 ℝ → ℂ) rfl
  · exact h.rec2
  · exact h.sym2
  · convert h.rec3 using 1 <;> simp [second, charData]
    ring
  · exact h.sym3
  · exact h.landing10 f
  · exact RealBlockJacquet.continuous_coe _
  · exact RealBlockJacquet.continuous_coe _
  · intro g hg k
    exact blockFourierCoefficient_blockFrobMap h.data20 _ hg k
  · intro g hg k
    exact blockFourierCoefficient_blockFrobMap h.data3 _ hg k

/-- The character-first route establishes the final e-block Fourier condition. -/
theorem landing4_e (f : KF (src d e)) :
    ∀ g ∈ unitaryCompact ℝ 4, ∀ k : ℤ, |k| < |e.weight| →
      blockFourierCoefficient 4 0 k (h.to4 f : Langlands.GeneralLinear 4 ℝ → ℂ) g = 0 := by
  have hz := RealSwapLandingInStages.realSwapLandingInStages.2 4 [] [.character (second d)]
    (first d) e (δ + (d.weight.natAbs : ℂ)) μ₀ μ₃
    (h.to12 f : Langlands.GeneralLinear 4 ℝ → ℂ)
    (blockFrobMap h.data02 (h.to12 f) : Langlands.GeneralLinear 4 ℝ → ℂ)
    (blockFrobMap h.data3 (blockFrobMap h.data02 (h.to12 f)) :
      Langlands.GeneralLinear 4 ℝ → ℂ) rfl
    (isRecurrent_congr h.rec0 (by dsimp [first, charData]; rw [Int.even_iff]; omega))
    (isSymmetric_congr h.sym0 (by dsimp [first, charData]; rw [Int.even_iff]; omega)
      (neg_one_pow_congr (by dsimp [first, charData]; omega)))
    (isRecurrent_congr h.rec3 (by dsimp [first, charData]; exact even_sub_mod _))
    (isSymmetric_congr h.sym3 (by dsimp [first, charData]; exact even_sub_mod _)
      (neg_one_pow_congr (by dsimp [first, charData]; omega)))
    (h.landing12 f) (RealBlockJacquet.continuous_coe _) (RealBlockJacquet.continuous_coe _)
    (fun g hg k => blockFourierCoefficient_blockFrobMap h.data02 _ hg k)
    (fun g hg k => blockFourierCoefficient_blockFrobMap h.data3 _ hg k)
  change ∀ g ∈ unitaryCompact ℝ 4, ∀ k : ℤ, |k| < |e.weight| →
    blockFourierCoefficient 4 0 k
      (blockFrobMap h.data3 (h.to3 f) : Langlands.GeneralLinear 4 ℝ → ℂ) g = 0
  rw [h.to3_eq f]
  exact hz

/-- Both recovered Fourier constraints put the four-crossing output in the actual target. -/
theorem landing (f : KF (src d e)) :
    (h.to4 f : Langlands.GeneralLinear 4 ℝ → ℂ) ∈ KF (dst d e) :=
  mem_dst (h.to4 f) (h.landing4_d f) (h.landing4_e f)

/-- The four-crossing Frobenius map between the two actual induced-pair modules. -/
def swap : KF (src d e) →ₗ[ℂ] KF (dst d e) :=
  LinearMap.codRestrict (KF (dst d e)) ((KF (l4 d e)).subtype.comp h.to4) h.landing

@[simp]
theorem swap_apply_coe (f : KF (src d e)) :
    (h.swap f : Langlands.GeneralLinear 4 ℝ → ℂ) = h.to4 f := rfl

end MultiplierData

end RealInducedPairFrobenius

/-- Four recurrent character crossings preserve both exchanged induction constraints. -/
def RealInducedPairFrobeniusLandingStatement : Prop :=
  ∀ (d e : ComplexCharacterData) (δ : ℂ) (μ₁ μ₀ μ₂ μ₃ : ℤ → ℂ)
    (h : RealInducedPairFrobenius.MultiplierData d e δ μ₁ μ₀ μ₂ μ₃)
    (f : RealInducedPairFrobenius.KF (RealInducedPairFrobenius.src d e)),
    (h.to4 f : Langlands.GeneralLinear 4 ℝ → ℂ) ∈
      RealInducedPairFrobenius.KF (RealInducedPairFrobenius.dst d e)

theorem realInducedPairFrobeniusLanding : RealInducedPairFrobeniusLandingStatement := by
  intro d e δ μ₁ μ₀ μ₂ μ₃ h f
  exact h.landing f

end Langlands.Archimedean

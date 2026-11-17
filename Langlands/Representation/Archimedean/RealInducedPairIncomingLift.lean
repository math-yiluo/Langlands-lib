import Langlands.Representation.Archimedean.RealInducedPairLinkedIncoming

/-! # Explicit lifting through the last three incoming crossings -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

namespace RealInducedPairIncomingLift

open RealBlockFrobeniusMap RealBlockMultiplier RealSwapLandingMirror
open RealInducedPairFrobenius RealInducedPairLinkedReplacement
open RealInducedPairLinkedIncoming RealStandardFiltration

section Middle

variable {d e : ComplexCharacterData} {δ : ℂ} {μ₁ μ₀ μ₂ μ₃ : ℤ → ℂ}
  (hdata : MultiplierData d e δ μ₁ μ₀ μ₂ μ₃)

include hdata

/-- The left middle crossing with the pointwise inverse multiplier. -/
theorem inverseData0 : IsBlockFrobData 4 (l10 d e) (l1 d e) 0
    ((d.weight.natAbs + e.weight.natAbs + 2 : ℕ) : ℤ)
    ((-1 : ℂ) ^ (d.weight.natAbs + e.weight.natAbs + 2))
    (fun j => (μ₀ j)⁻¹) := by
  apply characterSwapData (pre := [])
    (post := [.character (second d), .character (second e)])
    (c := first e) (b := first d) rfl
    (by dsimp [first, RealJacquetFrobenius.charData]; omega)
  simpa only [← inv_pow, inv_neg, inv_one] using hdata.sym0.inv

/-- The right middle crossing with the pointwise inverse multiplier. -/
theorem inverseData20 : IsBlockFrobData 4 (l3 d e) (l10 d e) 2 0 1
    (fun j => (μ₂ j)⁻¹) := by
  apply characterSwapData (pre := [.character (first e), .character (first d)])
    (post := []) (c := second e) (b := second d) (ε := 0) rfl rfl
  simpa only [inv_one, Nat.cast_zero, pow_zero] using hdata.sym2.inv

def middle : KF (l1 d e) →ₗ[ℂ] KF (l3 d e) :=
  (blockFrobMap hdata.data20).comp (blockFrobMap hdata.data0)

def inverseMiddle : KF (l3 d e) →ₗ[ℂ] KF (l1 d e) :=
  (blockFrobMap (inverseData0 hdata)).comp (blockFrobMap (inverseData20 hdata))

variable
  (hn0 : ∀ j : ℤ, Even (j - ((d.weight.natAbs + e.weight.natAbs + 2 : ℕ) : ℤ)) →
    μ₀ j ≠ 0)
  (hn2 : ∀ j : ℤ, Even j → μ₂ j ≠ 0)

include hn0 hn2

theorem middle_inverseMiddle (f : KF (l3 d e)) :
    middle hdata (inverseMiddle hdata f) = f := by
  change blockFrobMap hdata.data20
    (blockFrobMap hdata.data0
      (blockFrobMap (inverseData0 hdata) (blockFrobMap (inverseData20 hdata) f))) = f
  rw [RealCharacterInducedPushforward.frob_inv_of_ne_zero
    hdata.data0 (inverseData0 hdata) hn0]
  exact RealCharacterInducedPushforward.frob_inv_of_ne_zero
    hdata.data20 (inverseData20 hdata) (fun j hj => hn2 j (by simpa using hj)) f

theorem inverseMiddle_middle (f : KF (l1 d e)) :
    inverseMiddle hdata (middle hdata f) = f := by
  change blockFrobMap (inverseData0 hdata)
    (blockFrobMap (inverseData20 hdata)
      (blockFrobMap hdata.data20 (blockFrobMap hdata.data0 f))) = f
  have hr (g : KF (l10 d e)) :
      blockFrobMap (inverseData20 hdata) (blockFrobMap hdata.data20 g) = g := by
    apply blockFrobMap_blockFrobMap_eq
    intro j hj hne
    exact (hne (inv_mul_cancel₀ (hn2 j (by simpa using hj)))).elim
  rw [hr]
  apply blockFrobMap_blockFrobMap_eq
  intro j hj hne
  exact (hne (inv_mul_cancel₀ (hn0 j hj))).elim

/-- Both nonvanishing middle crossings form an actual equivalence of the
full-character spaces, with the displayed inverse. -/
def middleEquiv : KF (l1 d e) ≃ₗ[ℂ] KF (l3 d e) :=
  LinearEquiv.ofLinearMap (middle hdata) (inverseMiddle hdata)
    (LinearMap.ext (middle_inverseMiddle hdata hn0 hn2))
    (LinearMap.ext (inverseMiddle_middle hdata hn0 hn2))

theorem ker_to3_eq_ker_to1 :
    LinearMap.ker hdata.to3 = LinearMap.ker hdata.to1 := by
  ext f
  change middle hdata (hdata.to1 f) = 0 ↔ hdata.to1 f = 0
  exact (middleEquiv hdata hn0 hn2).map_eq_zero_iff

end Middle

section Linked

variable {d e : ComplexCharacterData} {k : ℕ}
  (h : IsLinkedAt d e k)
  (hp : Even ((outerWeight d e k : ℤ) - (e.weight.natAbs : ℤ)))
  {μ₁ μ₀ μ₂ : ℤ → ℂ}
  (hdata : MultiplierData e d (swapParameter e d) μ₁ μ₀ μ₂ (lastMultiplier d e k))

include hdata

/-- The inverse of the final binomial on the full character space. -/
theorem inverseLastData : IsBlockFrobData 4 (l0 d e) (l3 e d) 1
    ((e.weight.natAbs + 1 : ℕ) : ℤ) ((-1 : ℂ) ^ (e.weight.natAbs + 1))
    (fun j => (lastMultiplier d e k j)⁻¹) := by
  apply characterSwapData (pre := [.character (first d)])
    (post := [.character (second e)])
    (c := second d) (b := first e) rfl
    (by simp [first, second, RealJacquetFrobenius.charData])
  simpa only [← inv_pow, inv_neg, inv_one] using hdata.sym3.inv

/-- The last three incoming crossings on their full-character source. -/
def suffix : KF (l1 e d) →ₗ[ℂ] KF (l0 d e) :=
  (blockFrobMap hdata.data3).comp (middle hdata)

/-- A specific full-character lift: inverse central binomial, followed by the
inverse right and left middle multipliers. -/
def lift : KF (l0 d e) →ₗ[ℂ] KF (l1 e d) :=
  (inverseMiddle hdata).comp (blockFrobMap (inverseLastData hdata))

include hp in
theorem last_inverse_on_low (f : KF (l0 d e))
    (hf : ∀ g ∈ unitaryCompact ℝ 4, ∀ j : ℤ, (outerWeight d e k : ℤ) ≤ |j| →
      blockFourierCoefficient 4 1 j (f : Langlands.GeneralLinear 4 ℝ → ℂ) g = 0) :
    blockFrobMap hdata.data3 (blockFrobMap (inverseLastData hdata) f) = f := by
  apply blockFrobMap_blockFrobMap_eq
  intro j hj hne g hg
  by_cases hjl : |j| < (outerWeight d e k : ℤ)
  · have he : (((e.weight.natAbs + 1) % 2 : ℕ) : ℤ) = 0 ∨
        (((e.weight.natAbs + 1) % 2 : ℕ) : ℤ) = 1 := by omega
    have hpar : Even ((outerWeight d e k : ℤ) - 1 -
        (((e.weight.natAbs + 1) % 2 : ℕ) : ℤ)) := by
      rw [Int.even_iff] at hp ⊢
      omega
    have hjp : Even (j - (((e.weight.natAbs + 1) % 2 : ℕ) : ℤ)) := by
      rw [Int.even_iff] at hj ⊢
      omega
    have hn : lastMultiplier d e k j ≠ 0 :=
      (binomialMultiplier_ne_zero_iff
        (RealInducedPairOuterTail.outerWeight_pos d e k) he hpar hjp).mpr hjl
    exact (hne (mul_inv_cancel₀ hn)).elim
  · exact hf g hg j (not_lt.mp hjl)

include hp in
theorem suffix_low (f : KF (l1 e d)) :
    ∀ g ∈ unitaryCompact ℝ 4, ∀ j : ℤ, (outerWeight d e k : ℤ) ≤ |j| →
      blockFourierCoefficient 4 1 j
        (suffix hdata f : Langlands.GeneralLinear 4 ℝ → ℂ) g = 0 := by
  intro g hg j hj
  change blockFourierCoefficient 4 1 j
    (blockFrobMap hdata.data3 (middle hdata f) : Langlands.GeneralLinear 4 ℝ → ℂ) g = 0
  rw [blockFourierCoefficient_blockFrobMap hdata.data3 _ hg]
  by_cases hjp : Even (j - ((e.weight.natAbs + 1 : ℕ) : ℤ))
  · have he : (((e.weight.natAbs + 1) % 2 : ℕ) : ℤ) = 0 ∨
        (((e.weight.natAbs + 1) % 2 : ℕ) : ℤ) = 1 := by omega
    have hpar : Even ((outerWeight d e k : ℤ) - 1 -
        (((e.weight.natAbs + 1) % 2 : ℕ) : ℤ)) := by
      rw [Int.even_iff] at hp ⊢
      omega
    have hjp' : Even (j - (((e.weight.natAbs + 1) % 2 : ℕ) : ℤ)) := by
      rw [Int.even_iff] at hjp ⊢
      omega
    have hz : lastMultiplier d e k j = 0 := by
      by_contra hne
      have hlt := (binomialMultiplier_ne_zero_iff
        (RealInducedPairOuterTail.outerWeight_pos d e k) he hpar hjp').mp hne
      omega
    rw [hz, zero_mul]
  · rw [RealBlockJacquet.blockFourierCoefficient_eq_zero_of_not_even
      hdata.data3.lt hdata.data3.par (middle hdata f) hjp g, mul_zero]

variable
  (hn0 : ∀ j : ℤ, Even (j - ((e.weight.natAbs + d.weight.natAbs + 2 : ℕ) : ℤ)) →
    μ₀ j ≠ 0)
  (hn2 : ∀ j : ℤ, Even j → μ₂ j ≠ 0)

include hp hn0 hn2

theorem suffix_lift (f : KF (l0 d e))
    (hf : ∀ g ∈ unitaryCompact ℝ 4, ∀ j : ℤ, (outerWeight d e k : ℤ) ≤ |j| →
      blockFourierCoefficient 4 1 j (f : Langlands.GeneralLinear 4 ℝ → ℂ) g = 0) :
    suffix hdata (lift hdata f) = f := by
  change blockFrobMap hdata.data3
    (middle hdata (inverseMiddle hdata (blockFrobMap (inverseLastData hdata) f))) = f
  rw [middle_inverseMiddle hdata hn0 hn2]
  exact last_inverse_on_low hp hdata f hf

/-- On the full-character source the last three crossings have exactly the
central-tail kernel as their range. -/
theorem range_suffix :
    LinearMap.range (suffix hdata) =
      LinearMap.ker (blockFrobMap (RealInducedPairOuterTail.dataTail h hp)) := by
  apply le_antisymm
  · rintro _ ⟨f, rfl⟩
    apply (RealInducedPairOuterTail.tail_eq_zero_iff
      (RealInducedPairOuterTail.outerWeight_pos d e k)
      (RealCharacterPair.pairParity_eq _ _) (RealInducedPairOuterTail.outer_parity hp)
      (RealCharacterPairReducible.neg_one_pow_sq_fin _)
      (RealInducedPairOuterTail.dataTail h hp) _).mpr
    exact suffix_low hp hdata f
  · intro f hf
    have hlow := (RealInducedPairOuterTail.tail_eq_zero_iff
      (RealInducedPairOuterTail.outerWeight_pos d e k)
      (RealCharacterPair.pairParity_eq _ _) (RealInducedPairOuterTail.outer_parity hp)
      (RealCharacterPairReducible.neg_one_pow_sq_fin _)
      (RealInducedPairOuterTail.dataTail h hp) f).mp hf
    exact ⟨lift hdata f, suffix_lift hp hdata hn0 hn2 f hlow⟩

/-- Every vector in the actual outer-tail kernel has this explicit
full-character lift through the last three incoming crossings. -/
theorem lift_actual_kernel (f : KF (src d e))
    (hf : RealInducedPairOuterTail.outerMap h hp f = 0) :
    suffix hdata (lift hdata (Submodule.inclusion (src_le_l0 d e) f)) =
      Submodule.inclusion (src_le_l0 d e) f :=
  suffix_lift hp hdata hn0 hn2 _
    ((RealInducedPairOuterTail.outerMap_eq_zero_iff h hp f).mp hf)

end Linked

end RealInducedPairIncomingLift

open RealInducedPairIncomingLift RealInducedPairLinkedIncoming
  RealInducedPairFrobenius RealInducedPairLinkedReplacement RealBlockFrobeniusMap in
/-- Explicit lifting through the full-character suffix of the resonant incoming
complex, without a range claim for its actual first crossing. -/
def RealInducedPairIncomingLiftStatement : Prop :=
  ∀ (d e : ComplexCharacterData) (k : ℕ) (h : IsLinkedAt d e k)
    (hp : Even ((outerWeight d e k : ℤ) - (e.weight.natAbs : ℤ))),
    ∃ μ₀ μ₂ : ℤ → ℂ,
    ∃ hdata : MultiplierData e d (swapParameter e d)
      (signedMultiplier (innerWeight d e k) (d.weight.natAbs + 1))
      μ₀ μ₂ (lastMultiplier d e k),
      (∀ j : ℤ, Even (j - ((e.weight.natAbs + d.weight.natAbs + 2 : ℕ) : ℤ)) →
        μ₀ j ≠ 0) ∧
      (∀ j : ℤ, Even j → μ₂ j ≠ 0) ∧
      LinearMap.ker hdata.to3 = LinearMap.ker hdata.to1 ∧
      LinearMap.range (suffix hdata) =
        LinearMap.ker (blockFrobMap (RealInducedPairOuterTail.dataTail h hp)) ∧
      ∀ f : KF (src d e), RealInducedPairOuterTail.outerMap h hp f = 0 →
        suffix hdata (lift hdata (Submodule.inclusion (src_le_l0 d e) f)) =
          Submodule.inclusion (src_le_l0 d e) f

open RealInducedPairIncomingLift RealInducedPairLinkedIncoming in
theorem realInducedPairIncomingLift : RealInducedPairIncomingLiftStatement := by
  intro d e k h hp
  obtain ⟨μ₀, μ₂, hdata, hn0, hn2⟩ := exists_multiplierData h hp
  exact ⟨μ₀, μ₂, hdata, hn0, hn2, ker_to3_eq_ker_to1 hdata hn0 hn2,
    range_suffix h hp hdata hn0 hn2, lift_actual_kernel h hp hdata hn0 hn2⟩

end Langlands.Archimedean

import Langlands.Representation.Archimedean.RealCharacterInducedWeightZero
import Langlands.Representation.Archimedean.RealCharacterPairFiltration
import Langlands.Representation.Archimedean.RealInducedCharacterHard
import Langlands.Representation.Archimedean.RealInducedCharacterPushforward
import Langlands.Representation.Archimedean.RealInducedPairFiltrationReduction

/-!
# The induced–character filtration on `GL₃(ℝ)`
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

namespace RealStandardFiltration

/-- **Weight `0`.** Given the filtration statement for two characters, the standard module on
`GL₃(ℝ)` of an induction block `d` of weight `0` followed by a character `c` with
`Re t(d) < Re t(c)` has a filtration as in `RealAdjacentFiltration`. -/
theorem realAdjacentFiltration_induced_character_of_weight_eq_zero
    (hC : RealCharacterPairFiltrationStatement) (d : ComplexCharacterData)
    (c : RealCharacterData) (hw : d.weight = 0)
    (hdc : realBlockExponent (.induced d) < realBlockExponent (.character c)) :
    RealAdjacentFiltration 3 [] [] (.induced d) (.character c) := by
  let c1 := RealJacquetFrobenius.charData 1 d.exponent
  let c2 := RealJacquetFrobenius.charData 0 d.exponent
  have hexp : realBlockExpand (.induced d) = [.character c1, .character c2] := by
    simp [realBlockExpand, hw, c1, c2]
  have hKF : KF 3 [.character c1, .character c2, .character c] =
      KF 3 [.induced d, .character c] := by
    have h := kf_append_expand 3 [] [.character c] (.induced d)
    rw [hexp] at h
    exact h.symm
  have hKF' : KF 3 [.character c, .induced d] =
      KF 3 [.character c, .character c1, .character c2] := by
    have h := kf_append_expand 3 [.character c] [] (.induced d)
    rw [hexp] at h
    exact h
  have h1 : realBlockExponent (.character c1) < realBlockExponent (.character c) := hdc
  have h2 : realBlockExponent (.character c2) < realBlockExponent (.character c) := hdc
  have hsuppD : realExponentSupport [.induced d, .character c] =
      [d.exponent, d.exponent, c.exponent] := by
    simp [realExponentSupport, realBlockSupport, hw]
  have hsupp1 : realExponentSupport [.character c1, .character c] = [d.exponent, c.exponent] :=
    rfl
  have hsupp2 : realExponentSupport [.character c2, .character c] = [d.exponent, c.exponent] :=
    rfl
  have hsuppc1 : realExponentSupport [.character c1] = [d.exponent] := rfl
  have hsuppc2 : realExponentSupport [.character c2] = [d.exponent] := rfl
  have hwD : realWeightSquareSum [.induced d, .character c] = 0 := by
    simp [realWeightSquareSum, realBlockWeightSquare, hw]
  have hwc1 : realWeightSquareSum [.character c1] = 0 := rfl
  have hwc2 : realWeightSquareSum [.character c2] = 0 := rfl
  rw [realAdjacentFiltration_iff]
  have F1 := (realAdjacentFiltration_iff 3 [.character c1] [] (.character c2)
    (.character c)).1 (hC 3 [.character c1] [] c2 c (by simp [realRank, RealBlock.rank]) h2)
  refine (F1.bind fun es hes => ?_).congr hKF
  obtain ⟨ws, rfl, hws⟩ := hes
  rcases hws with rfl | ⟨hperm, hlt⟩
  · -- the piece `[c₁, χ, c₂]`: filter it again by the pair `[c₁, χ]`
    have F2 := (realAdjacentFiltration_iff 3 [] [.character c2] (.character c1)
      (.character c)).1
        (hC 3 [] [.character c2] c1 c (by simp [realRank, RealBlock.rank]) h1)
    refine F2.of_eq_pieces fun es hes => ?_
    obtain ⟨ws', rfl, hws'⟩ := hes
    rcases hws' with rfl | ⟨hperm', hlt'⟩
    · -- the piece `[χ, c₁, c₂] = [χ, D]`
      exact ⟨[.character c, .induced d], ⟨[.character c, .induced d], rfl, Or.inl rfl⟩, hKF'⟩
    · -- a piece `ws' ++ [c₂]` with a block of nonzero weight
      refine ⟨_, ⟨ws' ++ [.character c2], by simp, Or.inr ⟨?_, ?_⟩⟩, rfl⟩
      · rw [hsuppD, realExponentSupport_append, hsuppc2]
        rw [hsupp1] at hperm'
        exact (hperm'.append_right _).trans (List.Perm.cons _ (List.Perm.swap _ _ _))
      · rw [hwD, realWeightSquareSum_append, hwc2]
        omega
  · -- a piece `[c₁] ++ ws` with a block of nonzero weight
    refine HasFiltration.self ⟨.character c1 :: ws, by simp, Or.inr ⟨?_, ?_⟩⟩
    · rw [hsuppD, ← List.singleton_append, realExponentSupport_append, hsuppc1]
      rw [hsupp2] at hperm
      exact hperm.cons _
    · rw [hwD, ← List.singleton_append, realWeightSquareSum_append, hwc1]
      omega

end RealStandardFiltration

namespace RealInducedCharacter

open RealCharacterPairReducible RealBlockMultiplier RealCharacterPair

/-! ## The arithmetic of the case split -/

section Arithmetic

theorem stage1_int {ε : ℤ} {N : ℂ} {z : ℤ} (hε : 0 ≤ ε) (hz : N = z)
    (h : z = 0 ∨ Even (z - ε)) :
    (∀ i : ℕ, (ε : ℂ) + 2 * i + 1 + N ≠ 0) ∧ (∀ m : ℕ, N ≠ (ε : ℂ) + 2 * m + 1) := by
  refine ⟨fun i hi => ?_, fun m hm => ?_⟩
  · rw [hz] at hi
    have : ε + 2 * (i : ℤ) + 1 + z = 0 := by exact_mod_cast hi
    rcases h with h | ⟨r, hr⟩ <;> omega
  · rw [hz] at hm
    have : z = ε + 2 * (m : ℤ) + 1 := by exact_mod_cast hm
    rcases h with h | ⟨r, hr⟩ <;> omega

theorem stage1_nonint {ε : ℤ} {N : ℂ} (h : ∀ z : ℤ, N ≠ z) :
    (∀ i : ℕ, (ε : ℂ) + 2 * i + 1 + N ≠ 0) ∧ (∀ m : ℕ, N ≠ (ε : ℂ) + 2 * m + 1) :=
  ⟨fun i hi => h (-(ε + 2 * i + 1)) (by push_cast; linear_combination hi),
    fun m hm => h (ε + 2 * m + 1) (by push_cast; exact hm)⟩

theorem stage2_int {ε : ℤ} {N : ℂ} {w : ℤ} (hw : N = w) (h : Even (w - ε)) :
    ∀ m : ℕ, N ≠ (ε : ℂ) + 2 * m + 1 := fun m hm => by
  rw [hw] at hm
  have : w = ε + 2 * (m : ℤ) + 1 := by exact_mod_cast hm
  obtain ⟨r, hr⟩ := h
  omega

theorem stage2_nonint {ε : ℤ} {N N' : ℂ} {l : ℕ} (h : ∀ z : ℤ, N ≠ z) (hN : N' = N + l) :
    ∀ m : ℕ, N' ≠ (ε : ℂ) + 2 * m + 1 := fun m hm =>
  h (ε + 2 * m + 1 - l) (by push_cast; linear_combination hm - hN)

theorem re_aExp (d : ComplexCharacterData) :
    (aExp d).re = d.exponent.re + (d.weight.natAbs : ℝ) / 2 := by
  have : (d.weight.natAbs : ℂ) / 2 = (((d.weight.natAbs : ℝ) / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [aExp, Complex.add_re, this, Complex.ofReal_re]

end Arithmetic

/-! ## The case split -/

/-- **The case split.** Given the landing statement `RealSwapLandingInducedFirstStatement` and
the filtration in the remaining case `t_c - a = -m'` with `m' ≥ 1` an integer (where
`a = t_d + |m|/2`; then `2m' < |m|`), the induced–character filtration statement holds. -/
theorem realInducedCharacterFiltration_of_hard (hL : RealSwapLandingInducedFirstStatement)
    (hhard : ∀ (d : ComplexCharacterData) (c : RealCharacterData) (m' : ℕ), 0 < m' →
      2 * m' < d.weight.natAbs → c.exponent - aExp d = -(m' : ℂ) →
      realBlockExponent (.induced d) < realBlockExponent (.character c) →
      RealAdjacentFiltration 3 [] [] (.induced d) (.character c)) :
    RealInducedCharacterFiltrationStatement := by
  intro d c hdc
  by_cases hw : d.weight = 0
  · exact RealStandardFiltration.realAdjacentFiltration_induced_character_of_weight_eq_zero
      realCharacterPairFiltration d c hw hdc
  have hl : 0 < d.weight.natAbs := Int.natAbs_pos.mpr hw
  have hre₂ := re_bExp_lt (d := d) (c := c) hdc
  have hNb : c.exponent - bExp d = (c.exponent - aExp d) + (d.weight.natAbs : ℂ) := by
    linear_combination aExp_sub_bExp d
  by_cases hint : ∃ z : ℤ, c.exponent - aExp d = z
  · obtain ⟨z, hz⟩ := hint
    rcases lt_trichotomy z 0 with hneg | hzero | hpos
    · -- the hard case `z = -m'`
      obtain ⟨m', rfl⟩ : ∃ m' : ℕ, z = -(m' : ℤ) := ⟨z.natAbs, by omega⟩
      refine hhard d c m' (by omega) ?_ (by rw [hz]; push_cast; ring) hdc
      have hre : (c.exponent - aExp d).re = -(m' : ℝ) := by rw [hz]; simp
      rw [Complex.sub_re, re_aExp] at hre
      have h1 : d.exponent.re < c.exponent.re := hdc
      have h2 : (2 * m' : ℝ) < d.weight.natAbs := by linarith
      exact_mod_cast h2
    · -- `z = 0`: both swaps generic
      subst hzero
      let sb : Fin 2 := ⟨(d.weight.natAbs + c.parity.val) % 2, Nat.mod_lt _ two_pos⟩
      let sa : Fin 2 := ⟨(d.weight.natAbs + 1 + sb.val) % 2, Nat.mod_lt _ two_pos⟩
      have hs : (sa.val + sb.val) % 2 = (d.weight.natAbs + 1) % 2 := by
        simp only [sa, sb]
        omega
      obtain ⟨hden₁, hne₁⟩ := stage1_int (ε := pairParity (ca d sa) c)
        (by unfold pairParity; omega) hz (Or.inl rfl)
      refine pushforward_generic hL hl hs hden₁ hne₁ hre₂ ?_
      refine stage2_int (w := d.weight.natAbs)
        (by rw [hNb, hz, Int.cast_natCast, Int.cast_zero, zero_add]) ?_
      rw [Int.even_iff]
      simp only [pairParity, cb_parity, sb, Fin.val_mk]
      omega
    · -- `z = k ≥ 1`: the second swap is reducible with `ℓ = k + |m|`
      obtain ⟨k, rfl⟩ : ∃ k : ℕ, z = k := ⟨z.toNat, by omega⟩
      let sa : Fin 2 := ⟨(k + c.parity.val) % 2, Nat.mod_lt _ two_pos⟩
      let sb : Fin 2 := ⟨(d.weight.natAbs + 1 + sa.val) % 2, Nat.mod_lt _ two_pos⟩
      have hs : (sa.val + sb.val) % 2 = (d.weight.natAbs + 1) % 2 := by
        simp only [sa, sb]
        omega
      obtain ⟨hden₁, hne₁⟩ := stage1_int (ε := pairParity (ca d sa) c)
        (by unfold pairParity; omega) hz (Or.inr (by
          rw [Int.even_iff]
          simp only [pairParity, ca_parity, sa, Fin.val_mk]
          omega))
      refine pushforward_reducible hL hl hs hden₁ hne₁ (ℓ := k + d.weight.natAbs)
        (by omega) ?_ (by rw [hNb, hz]; push_cast; ring)
      rw [Int.even_iff]
      simp only [pairParity, cb_parity, sb, sa, Fin.val_mk]
      omega
  · -- `t_c - a` is not an integer: both swaps generic
    push Not at hint
    let sb : Fin 2 := ⟨(d.weight.natAbs + 1) % 2, Nat.mod_lt _ two_pos⟩
    have hs : ((0 : Fin 2).val + sb.val) % 2 = (d.weight.natAbs + 1) % 2 := by
      simp only [sb, Fin.val_zero]
      omega
    obtain ⟨hden₁, hne₁⟩ := stage1_nonint (ε := pairParity (ca d 0) c) hint
    exact pushforward_generic hL hl hs hden₁ hne₁ hre₂ (stage2_nonint hint hNb)

/-! ## The filtration statement from the landing statements -/

/-- **The induced–character filtration from the landing statements.** Given the two landing
statements `RealSwapLandingInducedFirstStatement` and `RealSwapLandingCharacterFirstStatement`,
the induced–character filtration statement holds: the case split
`realInducedCharacterFiltration_of_hard` with the hard case supplied by `hard_filtration`. -/
theorem realInducedCharacterFiltration_of_landing (hL : RealSwapLandingInducedFirstStatement)
    (hL' : RealSwapLandingCharacterFirstStatement) : RealInducedCharacterFiltrationStatement :=
  realInducedCharacterFiltration_of_hard hL fun _ _ _ hm' hml hN _ =>
    hard_filtration hL hL' hm' hml hN

end RealInducedCharacter

end Langlands.Archimedean

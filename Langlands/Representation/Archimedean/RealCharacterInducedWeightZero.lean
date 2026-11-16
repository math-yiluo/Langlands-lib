import Langlands.Representation.Archimedean.RealStandardFiltration
import Langlands.Representation.Archimedean.RealUnlinkedSwapReduction

/-!
# The character–induced filtration on `GL₃(ℝ)` for an induction block of weight `0`

An induction block `D` of weight `0` and exponent `t` has the same standard module as the two
character blocks `c₁ = sgn |·|^t`, `c₂ = |·|^t` (`realStandardModule_append_expand`). For a
character `χ` with `Re t(χ) < Re t`, two applications of the filtration statement for two
characters, first to `[χ, c₁]` and then to `[χ, c₂]`, filter the standard module of
`[χ, c₁, c₂] = [χ, D]`; refining the pieces (`HasFiltration.bind`) gives a filtration as in
`RealAdjacentFiltration 3 [] [] χ D`.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

namespace RealStandardFiltration

/-- Expanding a block does not change the `O(n)`-finite functions. -/
theorem kf_append_expand (n : ℕ) (pre post : List RealBlock) (x : RealBlock) :
    KF n (pre ++ x :: post) = KF n (pre ++ realBlockExpand x ++ post) := by
  simp only [KF, realStandardModule_append_expand]

/-- **Weight `0`.** Given the filtration statement for two characters, the standard module on
`GL₃(ℝ)` of a character `c` followed by an induction block `d` of weight `0` with
`Re t(c) < Re t(d)` has a filtration as in `RealAdjacentFiltration`. -/
theorem realAdjacentFiltration_character_induced_of_weight_eq_zero
    (hC : RealCharacterPairFiltrationStatement) (c : RealCharacterData)
    (d : ComplexCharacterData) (hw : d.weight = 0)
    (hcd : realBlockExponent (.character c) < realBlockExponent (.induced d)) :
    RealAdjacentFiltration 3 [] [] (.character c) (.induced d) := by
  let c1 := RealJacquetFrobenius.charData 1 d.exponent
  let c2 := RealJacquetFrobenius.charData 0 d.exponent
  have hexp : realBlockExpand (.induced d) = [.character c1, .character c2] := by
    simp [realBlockExpand, hw, c1, c2]
  have hKF : KF 3 [.character c, .character c1, .character c2] =
      KF 3 [.character c, .induced d] := by
    have h := kf_append_expand 3 [.character c] [] (.induced d)
    rw [hexp] at h
    exact h.symm
  have hKF' : KF 3 [.induced d, .character c] =
      KF 3 [.character c1, .character c2, .character c] := by
    have h := kf_append_expand 3 [] [.character c] (.induced d)
    rw [hexp] at h
    exact h
  have h1 : realBlockExponent (.character c) < realBlockExponent (.character c1) := hcd
  have h2 : realBlockExponent (.character c) < realBlockExponent (.character c2) := hcd
  have hsuppD : realExponentSupport [.character c, .induced d] =
      [c.exponent, d.exponent, d.exponent] := by
    simp [realExponentSupport, realBlockSupport, hw]
  have hsupp1 : realExponentSupport [.character c, .character c1] = [c.exponent, d.exponent] :=
    rfl
  have hsupp2 : realExponentSupport [.character c, .character c2] = [c.exponent, d.exponent] :=
    rfl
  have hsuppc1 : realExponentSupport [.character c1] = [d.exponent] := rfl
  have hsuppc2 : realExponentSupport [.character c2] = [d.exponent] := rfl
  have hwD : realWeightSquareSum [.character c, .induced d] = 0 := by
    simp [realWeightSquareSum, realBlockWeightSquare, hw]
  have hwc1 : realWeightSquareSum [.character c1] = 0 := rfl
  have hwc2 : realWeightSquareSum [.character c2] = 0 := rfl
  rw [realAdjacentFiltration_iff]
  have F1 := (realAdjacentFiltration_iff 3 [] [.character c2] (.character c)
    (.character c1)).1 (hC 3 [] [.character c2] c c1 (by simp [realRank, RealBlock.rank]) h1)
  refine (F1.bind fun es hes => ?_).congr hKF
  obtain ⟨ws, rfl, hws⟩ := hes
  rcases hws with rfl | ⟨hperm, hlt⟩
  · -- the piece `[c₁, χ, c₂]`: filter it again by the pair `[χ, c₂]`
    have F2 := (realAdjacentFiltration_iff 3 [.character c1] [] (.character c)
      (.character c2)).1
        (hC 3 [.character c1] [] c c2 (by simp [realRank, RealBlock.rank]) h2)
    refine F2.of_eq_pieces fun es hes => ?_
    obtain ⟨ws', rfl, hws'⟩ := hes
    rcases hws' with rfl | ⟨hperm', hlt'⟩
    · -- the piece `[c₁, c₂, χ] = [D, χ]`
      exact ⟨[.induced d, .character c], ⟨[.induced d, .character c], rfl, Or.inl rfl⟩, hKF'⟩
    · -- a piece `[c₁] ++ ws'` with a block of nonzero weight
      refine ⟨_, ⟨.character c1 :: ws', by simp, Or.inr ⟨?_, ?_⟩⟩, rfl⟩
      · rw [hsuppD, ← List.singleton_append, realExponentSupport_append, hsuppc1]
        rw [hsupp2] at hperm'
        exact ((hperm'.cons d.exponent).trans (List.Perm.swap _ _ _))
      · rw [hwD, ← List.singleton_append, realWeightSquareSum_append, hwc1]
        omega
  · -- a piece `ws ++ [c₂]` with a block of nonzero weight
    refine HasFiltration.self ⟨ws ++ [.character c2], by simp, Or.inr ⟨?_, ?_⟩⟩
    · rw [hsuppD, realExponentSupport_append, hsuppc2]
      rw [hsupp1] at hperm
      exact hperm.append_right _
    · rw [hwD, realWeightSquareSum_append, hwc2]
      omega

end RealStandardFiltration

end Langlands.Archimedean

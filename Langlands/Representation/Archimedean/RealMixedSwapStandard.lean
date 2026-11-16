import Langlands.Representation.Archimedean.RealMixedSwapSigned

/-!
# Signed reversal on the mixed real standard modules
-/

noncomputable section

namespace Langlands.Archimedean.RealMixedSwapTwist

open Langlands.LocalFactor.Archimedean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

theorem mem_inducedCharacter_iff (d : ComplexCharacterData) (b : RealCharacterData)
    (f : G → ℂ) :
    f ∈ realStandardModule 3 [.induced d, .character b] ↔
      f ∈ principalSeries ℝ 3 (realPositionCharacter [.induced d, .character b]) ∧
        ∀ k : ℤ, |k| < |d.weight| → ∀ g, blockFourierCoefficient 3 0 k f g = 0 := by
  constructor
  · intro hf
    exact ⟨hf.1, hf.2 0 d rfl⟩
  · rintro ⟨hf, hvan⟩
    refine ⟨hf, ?_⟩
    intro p e he
    have hp : p + 1 < 3 := by
      simpa only [realRank_cons, realRank_nil, RealBlock.rank] using realInducedBlockAt_lt he
    have hp' : p < 2 := by omega
    interval_cases p
    · have heq : d = e := Option.some.inj he
      subst e
      exact hvan
    · simp only [realInducedBlockAt] at he
      contradiction

theorem mem_characterInduced_iff (d : ComplexCharacterData) (b : RealCharacterData)
    (f : G → ℂ) :
    f ∈ realStandardModule 3 [.character b, .induced d] ↔
      f ∈ principalSeries ℝ 3 (realPositionCharacter [.character b, .induced d]) ∧
        ∀ k : ℤ, |k| < |d.weight| → ∀ g, blockFourierCoefficient 3 1 k f g = 0 := by
  constructor
  · intro hf
    exact ⟨hf.1, hf.2 1 d rfl⟩
  · rintro ⟨hf, hvan⟩
    refine ⟨hf, ?_⟩
    intro p e he
    have hp : p + 1 < 3 := by
      simpa only [realRank_cons, realRank_nil, RealBlock.rank] using realInducedBlockAt_lt he
    have hp' : p < 2 := by omega
    interval_cases p
    · simp only [realInducedBlockAt] at he
      contradiction
    · have heq : d = e := Option.some.inj he
      subst e
      exact hvan

theorem signedReverseCharacters_inverse (q : ℕ) {χ χ' : ℕ → ℝˣ → ℂ}
    (hχ' : ∀ (j : Fin 3) (x : ℝˣ), χ' j x = unitSign x ^ q * χ (Fin.rev j) x⁻¹)
    (j : Fin 3) (x : ℝˣ) :
    χ j x = unitSign x ^ q * χ' (Fin.rev j) x⁻¹ := by
  rw [hχ', Fin.rev_rev, inv_inv, unitSign_inv, ← mul_assoc, ← mul_pow, ← sq,
    unitSign_sq, one_pow, one_mul]

theorem signedTwistLin_mem_inducedCharacter (d : ComplexCharacterData) (b : RealCharacterData)
    {f : G → ℂ} (hf : f ∈ realStandardModule 3 [.induced d, .character b]) :
    signedTwistLin (mixedSignPower d) f ∈
      realStandardModule 3 [.character (reverseCharacter d b), .induced (reverseInduced d)] := by
  rcases (mem_inducedCharacter_iff d b f).mp hf with ⟨hps, hvan⟩
  refine (mem_characterInduced_iff _ _ _).mpr
    ⟨signedTwistLin_mem_principalSeries _ (positionCharacter_induced_character d b) hps, ?_⟩
  intro k hk g
  have hcoeff : blockFourierCoefficient 3 1 k (signedTwistLin (mixedSignPower d) f) g =
      signDet g ^ mixedSignPower d * blockFourierCoefficient 3 0 k f (twist g) :=
    blockFourierCoefficient_signedTwistLin _ ⟨1, by decide⟩ k f g
  rw [hcoeff]
  rw [hvan k (by simpa only [reverseInduced_weight] using hk), mul_zero]

theorem signedTwistLin_mem_characterInduced (d : ComplexCharacterData) (b : RealCharacterData)
    {f : G → ℂ} (hf : f ∈ realStandardModule 3 [.character b, .induced d]) :
    signedTwistLin (mixedSignPower d) f ∈
      realStandardModule 3 [.induced (reverseInduced d), .character (reverseCharacter d b)] := by
  rcases (mem_characterInduced_iff d b f).mp hf with ⟨hps, hvan⟩
  refine (mem_inducedCharacter_iff _ _ _).mpr
    ⟨signedTwistLin_mem_principalSeries _ (positionCharacter_character_induced d b) hps, ?_⟩
  intro k hk g
  have hcoeff : blockFourierCoefficient 3 0 k (signedTwistLin (mixedSignPower d) f) g =
      signDet g ^ mixedSignPower d * blockFourierCoefficient 3 1 k f (twist g) :=
    blockFourierCoefficient_signedTwistLin _ ⟨0, by decide⟩ k f g
  rw [hcoeff]
  rw [hvan k (by simpa only [reverseInduced_weight] using hk), mul_zero]

theorem signedTwistLin_mem_inducedCharacter_inverse
    (d : ComplexCharacterData) (b : RealCharacterData) {f : G → ℂ}
    (hf : f ∈ realStandardModule 3
      [.character (reverseCharacter d b), .induced (reverseInduced d)]) :
    signedTwistLin (mixedSignPower d) f ∈
      realStandardModule 3 [.induced d, .character b] := by
  rcases (mem_characterInduced_iff _ _ f).mp hf with ⟨hps, hvan⟩
  refine (mem_inducedCharacter_iff d b _).mpr
    ⟨signedTwistLin_mem_principalSeries _
      (signedReverseCharacters_inverse _ (positionCharacter_induced_character d b)) hps, ?_⟩
  intro k hk g
  have hcoeff : blockFourierCoefficient 3 0 k (signedTwistLin (mixedSignPower d) f) g =
      signDet g ^ mixedSignPower d * blockFourierCoefficient 3 1 k f (twist g) :=
    blockFourierCoefficient_signedTwistLin _ ⟨0, by decide⟩ k f g
  rw [hcoeff]
  rw [hvan k (by simpa only [reverseInduced_weight] using hk), mul_zero]

theorem signedTwistLin_mem_characterInduced_inverse
    (d : ComplexCharacterData) (b : RealCharacterData) {f : G → ℂ}
    (hf : f ∈ realStandardModule 3
      [.induced (reverseInduced d), .character (reverseCharacter d b)]) :
    signedTwistLin (mixedSignPower d) f ∈
      realStandardModule 3 [.character b, .induced d] := by
  rcases (mem_inducedCharacter_iff _ _ f).mp hf with ⟨hps, hvan⟩
  refine (mem_characterInduced_iff d b _).mpr
    ⟨signedTwistLin_mem_principalSeries _
      (signedReverseCharacters_inverse _ (positionCharacter_character_induced d b)) hps, ?_⟩
  intro k hk g
  have hcoeff : blockFourierCoefficient 3 1 k (signedTwistLin (mixedSignPower d) f) g =
      signDet g ^ mixedSignPower d * blockFourierCoefficient 3 0 k f (twist g) :=
    blockFourierCoefficient_signedTwistLin _ ⟨1, by decide⟩ k f g
  rw [hcoeff]
  rw [hvan k (by simpa only [reverseInduced_weight] using hk), mul_zero]

/-- Signed reversal from an induction-character standard module to its reversed parameters. -/
def inducedCharacterSignedEquiv (d : ComplexCharacterData) (b : RealCharacterData) :
    kFiniteFunctions (realStandardModule 3 [.induced d, .character b]) (unitaryCompact ℝ 3)
      ≃ₗ[ℂ] kFiniteFunctions
        (realStandardModule 3
          [.character (reverseCharacter d b), .induced (reverseInduced d)])
        (unitaryCompact ℝ 3) where
  toFun f := ⟨signedTwistLin (mixedSignPower d) f,
    signedTwistLin_mem_inducedCharacter d b f.2.1,
    signedTwistLin_mem_kFiniteVectors _ f.2.2⟩
  invFun f := ⟨signedTwistLin (mixedSignPower d) f,
    signedTwistLin_mem_inducedCharacter_inverse d b f.2.1,
    signedTwistLin_mem_kFiniteVectors _ f.2.2⟩
  left_inv f := Subtype.ext (signedTwistLin_signedTwistLin _ f)
  right_inv f := Subtype.ext (signedTwistLin_signedTwistLin _ f)
  map_add' f h := Subtype.ext (map_add (signedTwistLin _) (f : G → ℂ) (h : G → ℂ))
  map_smul' c f := Subtype.ext (map_smul (signedTwistLin _) c (f : G → ℂ))

/-- Signed reversal from a character-induction standard module to its reversed parameters. -/
def characterInducedSignedEquiv (d : ComplexCharacterData) (b : RealCharacterData) :
    kFiniteFunctions (realStandardModule 3 [.character b, .induced d]) (unitaryCompact ℝ 3)
      ≃ₗ[ℂ] kFiniteFunctions
        (realStandardModule 3
          [.induced (reverseInduced d), .character (reverseCharacter d b)])
        (unitaryCompact ℝ 3) where
  toFun f := ⟨signedTwistLin (mixedSignPower d) f,
    signedTwistLin_mem_characterInduced d b f.2.1,
    signedTwistLin_mem_kFiniteVectors _ f.2.2⟩
  invFun f := ⟨signedTwistLin (mixedSignPower d) f,
    signedTwistLin_mem_characterInduced_inverse d b f.2.1,
    signedTwistLin_mem_kFiniteVectors _ f.2.2⟩
  left_inv f := Subtype.ext (signedTwistLin_signedTwistLin _ f)
  right_inv f := Subtype.ext (signedTwistLin_signedTwistLin _ f)
  map_add' f h := Subtype.ext (map_add (signedTwistLin _) (f : G → ℂ) (h : G → ℂ))
  map_smul' c f := Subtype.ext (map_smul (signedTwistLin _) c (f : G → ℂ))

@[simp] theorem inducedCharacterSignedEquiv_apply_coe
    (d : ComplexCharacterData) (b : RealCharacterData)
    (f : kFiniteFunctions (realStandardModule 3 [.induced d, .character b])
      (unitaryCompact ℝ 3)) :
    (inducedCharacterSignedEquiv d b f : G → ℂ) =
      signedTwistLin (mixedSignPower d) f := rfl

@[simp] theorem inducedCharacterSignedEquiv_symm_apply_coe
    (d : ComplexCharacterData) (b : RealCharacterData)
    (f : kFiniteFunctions (realStandardModule 3
      [.character (reverseCharacter d b), .induced (reverseInduced d)])
      (unitaryCompact ℝ 3)) :
    ((inducedCharacterSignedEquiv d b).symm f : G → ℂ) =
      signedTwistLin (mixedSignPower d) f := rfl

@[simp] theorem characterInducedSignedEquiv_apply_coe
    (d : ComplexCharacterData) (b : RealCharacterData)
    (f : kFiniteFunctions (realStandardModule 3 [.character b, .induced d])
      (unitaryCompact ℝ 3)) :
    (characterInducedSignedEquiv d b f : G → ℂ) =
      signedTwistLin (mixedSignPower d) f := rfl

@[simp] theorem characterInducedSignedEquiv_symm_apply_coe
    (d : ComplexCharacterData) (b : RealCharacterData)
    (f : kFiniteFunctions (realStandardModule 3
      [.induced (reverseInduced d), .character (reverseCharacter d b)])
      (unitaryCompact ℝ 3)) :
    ((characterInducedSignedEquiv d b).symm f : G → ℂ) =
      signedTwistLin (mixedSignPower d) f := rfl

end Langlands.Archimedean.RealMixedSwapTwist

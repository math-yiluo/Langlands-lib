import Langlands.Global.Arithmetic.CMHalfWeightCharacterProof
import Langlands.Global.Arithmetic.HarrisDatumArchimedean
import Langlands.Global.Arithmetic.HarrisProposition48ParityReductionStatement

/-! # Auxiliary parity normalization from arithmetic and local transport -/

universe uF

namespace Langlands.Global.Harris

open NumberField AdelicFunctoriality

private theorem isAlgebraicAfterTwist_mod_two_iff {K : Type} [Field K] [NumberField K]
    [IsTotallyComplex K] (a : ℕ) (χ : HeckeCharacter K) :
    IsAlgebraicAfterTwist (a % 2) χ ↔ IsAlgebraicAfterTwist a χ := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    rcases Nat.lt_or_ge a 2 with ha | ha
    · rw [Nat.mod_eq_of_lt ha]
    · obtain ⟨k, rfl⟩ : ∃ k, a = k + 2 := ⟨a - 2, by omega⟩
      rw [Nat.add_mod_right, isAlgebraicAfterTwist_add_two_iff]
      exact ih k (by omega)

/-- Correct the auxiliary inducing datum with a conjugate-inverse character of the base,
using the four arithmetic and local transport inputs. -/
theorem proposition48AuxiliaryParityNormalizationReduction :
    Proposition48AuxiliaryParityNormalizationReductionStatement.{uF} := by
  intro hinfty hnorm hplace hambient Q b hQ
  obtain ⟨he, hsplit, hscalar, hnormal, hp, hcompat, hu, huc, hgp, halg, hreg, hc, hχs⟩ := hQ
  let d := Module.finrank Q.E Q.E' - 1
  let m := (b + d) % 2
  obtain ⟨ν, hνc, hνalg, hνone⟩ : ∃ ν : HeckeCharacter Q.E,
      IsConjugateInverse ν ∧ IsAlgebraicAfterTwist m ν ∧ (b % 2 = d % 2 → ν = 1) := by
    by_cases h : b % 2 = d % 2
    · have hm : m = 0 := by dsimp only [m]; omega
      refine ⟨1, fun x ↦ by simp, ?_, fun _ ↦ rfl⟩
      rw [hm]
      refine ⟨fun _ ↦ 0, fun x ↦ ?_⟩
      simp [HeckeCharacter.atInfinity, HeckeCharacter.onIdeles, InfinityType.toCharacter_apply]
    · have hm : m = 1 := by dsimp only [m]; omega
      have : IsTotallyComplex Q.K₀ := hsplit.2.1
      let j : Q.K₀ →+* Q.E := Q.K₀.val.toRingHom
      let τ : Q.K₀ →+* ℂ := Classical.choice inferInstance
      let t : InfinityType Q.E := HarrisDatum.halfWeights (E := Q.E) j τ
      have ht : t.IsPureOfWeight 1 := HarrisDatum.halfWeights_pure hsplit.1 j τ
      obtain ⟨ν, hνc, hνinf, _⟩ := cmHalfWeightCharacter.{0} Q.E t ht ∅ (by simp)
      refine ⟨ν, hνc, ?_, fun heq ↦ (h heq).elim⟩
      rw [hm]
      exact ⟨t, fun x ↦ by simpa only [pow_one] using hνinf x⟩
  obtain ⟨halgTransport, hregTransport⟩ := hinfty Q.E Q.E' Q.ξ ν b m
  have hpar : (b + m) % 2 = d % 2 := by
    dsimp only [m]
    omega
  have hcorrectedAlg : IsAlgebraicAfterTwist d (Q.correctedCharacter ν) := by
    apply (isAlgebraicAfterTwist_mod_two_iff d _).mp
    rw [← hpar]
    exact (isAlgebraicAfterTwist_mod_two_iff (b + m) _).mpr (halgTransport halg hνalg)
  have hcorrectedConj : IsConjugateInverse (Q.correctedCharacter ν) := by
    refine HarrisDatum.isConjugateInverse_mul Q.ξ _ hc ?_
    intro x
    change ν (ideleClassNorm (K := Q.E) (ideleClassComplexConj x)) =
      (ν (ideleClassNorm (K := Q.E) x))⁻¹
    rw [hnorm Q.E Q.E' x]
    exact hνc _
  obtain ⟨χs, ψ, hχsc, hψ⟩ := hplace Q Q.Ps ν Q.χs he hp hcompat hχs
  have hgp' := hambient Q.F Q.F' _ _ ψ hψ hgp
  exact ⟨ν, χs, hνc, hνalg, hνone, he, hsplit, hscalar, hnormal, hp, hcompat, hu,
    huc, hgp', hcorrectedAlg, hregTransport hreg, hcorrectedConj, hχsc⟩

end Langlands.Global.Harris

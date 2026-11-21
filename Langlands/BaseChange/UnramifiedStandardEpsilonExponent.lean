import Langlands.BaseChange.CuspidalSigmaLiftConductorLocalReduction
import Langlands.LocalField.PadicBridge
import Langlands.Representation.RankinSelberg.HighlyRamified.ShellExpansion
import Langlands.Representation.RankinSelberg.UnramifiedTwistEpsilonProof
import Langlands.LocalField.Normalization.SpectralCharacter

/-! # Standard epsilon exponents under unramified determinant twists -/

noncomputable section

set_option autoImplicit false

universe u uV

namespace Langlands.BaseChange

open HarmonicAnalysis GeneralLinear RankinSelberg
open scoped PadicField.CanonicalLocalField

/-- A character trivial on the valuation units is a complex power of the
normalized absolute value. The value at the uniformizer determines the power
up to the period of the spectral parameter. -/
theorem exists_complex_absPower_of_isUnramifiedCharacter {p : ℕ} [Fact p.Prime]
    (F : PadicField.{u} p) (χ : F.Carrierˣ →* ℂˣ)
    (hχ : F.canonicalTopologicalData.IsUnramifiedCharacter χ) :
    ∃ s : ℂ, ∀ x : F.Carrierˣ, (χ x : ℂ) =
      ((F.canonicalTopologicalData.normalizedAbs (x : F.Carrier) : ℝ) : ℂ) ^ s := by
  let T := F.canonicalTopologicalData
  let a := χ T.uniformizerUnit
  have hq : 0 < (T.residueCardinality : ℝ) := by
    exact_mod_cast Nat.zero_lt_one.trans T.residueCardinality_gt_one
  obtain ⟨s, hs, -⟩ := HighlyRamified.exists_spectralPoint_eq T.residueCardinality_gt_one a.ne_zero
  have hs' : LocalFactor.spectralParameter T.residueCardinality hq s = a := by
    apply Units.ext
    rwa [← spectralPoint_eq_spectralParameter]
  have hc : χ = (T.normalizedAbsPowerCharacter s).toMonoidHom :=
    (T.eq_unramifiedCharacter χ hχ).trans (congrArg T.unramifiedCharacter hs'.symm)
  refine ⟨s, fun x => ?_⟩
  have hx := T.normalizedAbs_pos x.ne_zero
  calc
    (χ x : ℂ) = Complex.exp (s * (Real.log (T.normalizedAbs (x : F.Carrier)) : ℂ)) := by
      rw [hc]
      exact T.normalizedAbsPowerCharacter_apply s x
    _ = ((T.normalizedAbs (x : F.Carrier) : ℝ) : ℂ) ^ s := by
      rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), ← Complex.ofReal_log hx.le, mul_comm]

/-- For an arbitrary unramified character of the determinant, the actual standard
pair epsilon certificate has the same exponent after twisting. -/
def UnramifiedStandardEpsilonExponentStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
    {r : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (ρ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V) (χ : F.Carrierˣ →* ℂˣ),
    F.canonicalTopologicalData.IsUnramifiedCharacter χ →
    ∀ (e : ℂˣ × ℤ), IsEpsilonFactorAgainstTrivialCharacter ψ ν.val ρ e →
      ∃ e' : ℂˣ × ℤ, e'.2 = e.2 ∧
        IsEpsilonFactorAgainstTrivialCharacter ψ ν.val (Langlands.twist (χ.comp determinant) ρ) e'

/-- Express the unramified character by its uniformizer value and apply the
published epsilon shift formula with the trivial second representation. -/
theorem unramifiedStandardEpsilonExponent : UnramifiedStandardEpsilonExponentStatement.{u, uV} := by
  intro p _ F r V _ _ ψ ν ρ χ hχ e he
  let one := rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)
  obtain ⟨s, hs⟩ := exists_complex_absPower_of_isUnramifiedCharacter F χ hχ
  have hsym : IsPadicSymmetricEpsilonFactor F ψ ν.val ρ one e :=
    (isPadicSymmetricEpsilonFactor_of_le (Nat.zero_le r)).mpr he
  obtain ⟨e', he', -, -, ht⟩ := unramifiedTwistEpsilon p F ψ ν r 0 ρ one s χ hs e hsym
  exact ⟨e', he', (isPadicSymmetricEpsilonFactor_of_le (Nat.zero_le r)).mp ht⟩

end Langlands.BaseChange

import Langlands.Representation.Classification.SupercuspidalSupport
import Langlands.Representation.Smooth.Schur.Proof
import Langlands.LocalField.Uniformizer
import Langlands.LocalField.Normalization.Proof
import Langlands.Group.GL.NormalizedCharacter
import Langlands.Representation.Twist.RealPower

/-!
# A cuspidal datum is not fixed by the twist by `ν`

For every cuspidal datum `ρ`, the twist `ν ρ = ρ.twist 1` differs from `ρ`.
The head-shift step of the proof of Bernstein–Zelevinsky 1977, Theorem 4.11
(Case 2 of §4.15) uses this to exclude the block `ρ_{i₀}` itself. The proof is a
central-character argument: a positive-rank irreducible admissible representation
has a central character by Schur's lemma, and evaluating an equivalence with its
twist by `|det|^s` at the scalar uniformizer gives `q^{-rs} = 1`, hence `s = 0`.
-/

noncomputable section

namespace Langlands.Derivative.OrderedCuspidalProductTwistOne

open CategoryTheory GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- A positive-rank irreducible admissible representation is not equivalent to its
twist by `|det|^s` unless `s = 0`. -/
theorem exponent_eq_zero (r : ℕ) (hr : 0 < r)
    (A : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier))
    (hAa : letI := T.topology; A.IsAdmissible)
    (hAi : letI := T.topology; A.IsIrreducible) (s : ℝ)
    (e : letI := T.topology; A.representation.Equiv
      (twist (T.determinantPowerCharacter r s) A.representation)) :
    s = 0 := by
  let := T.topology
  let := T.generalLinearTopologicalGroup r
  let := hAi
  let : Nontrivial A := IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GeneralLinear r F.Carrier))
    A.representation.asModule
  obtain ⟨ω, ⟨_, hω⟩, _⟩ := admissibleSchur_centralCharacter A.representation hAa hAi
  let z := scalarToCenter (n := r) (LocalFactor.PadicAbelian.uniformizerUnit T)
  obtain ⟨v, hv⟩ := exists_ne (0 : A)
  have hev : e v ≠ 0 := fun h => hv (e.injective (by simpa using h))
  have he := Representation.IntertwiningMap.isIntertwining
    A.representation (twist (T.determinantPowerCharacter r s) A.representation)
    e.toIntertwiningMap (z : GeneralLinear r F.Carrier) v
  change e (A.representation (z : GeneralLinear r F.Carrier) v) =
    (T.determinantPowerCharacter r s (z : GeneralLinear r F.Carrier) : ℂ) •
      A.representation (z : GeneralLinear r F.Carrier) (e v) at he
  rw [hω, map_smul, hω, smul_smul] at he
  have hc : (ω z : ℂ) = (T.determinantPowerCharacter r s (z : GeneralLinear r F.Carrier) : ℂ) *
      (ω z : ℂ) := smul_left_injective ℂ hev he
  have hv1 : (T.determinantPowerCharacter r s (z : GeneralLinear r F.Carrier) : ℂ) = 1 :=
    mul_right_cancel₀ (ω z).ne_zero (by simpa using hc.symm)
  change (T.determinantPowerCharacter r s
    (scalar (LocalFactor.PadicAbelian.uniformizerUnit T)) : ℂ) = 1 at hv1
  rw [coe_realPowerCharacter, T.determinantNorm_scalar] at hv1
  simp only [Units.val_pow_eq_pow_val, NNReal.coe_pow,
    T.normalizedAbsUnits_coe, LocalFactor.PadicAbelian.uniformizerUnit_coe,
    T.normalizedAbs_uniformizer, zpow_neg_one] at hv1
  have hq : 1 < (T.residueCardinality : ℝ) := by exact_mod_cast T.residueCardinality_gt_one
  have hq0 : (0 : ℝ) ≤ T.residueCardinality := by positivity
  have hreal : ((T.residueCardinality : ℝ)⁻¹ ^ r) ^ s = 1 := by
    exact_mod_cast hv1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← Real.rpow_neg_one,
    ← Real.rpow_mul hq0] at hreal
  have hexp : -1 * (r : ℝ) * s = 0 := by
    have := (Real.rpow_right_inj (lt_trans zero_lt_one hq) (ne_of_gt hq)).mp
      (hreal.trans (Real.rpow_zero _).symm)
    simpa [mul_assoc] using this
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  rcases mul_eq_zero.mp hexp with h | h
  · exact absurd h (mul_ne_zero (by norm_num) hr0)
  · exact h

/-- `ν ρ ≠ ρ` for every cuspidal datum `ρ`. -/
theorem twist_one_ne_self (ρ : T.CuspidalDatum.{uV, uF}) : ρ.twist 1 ≠ ρ := by
  let := T.topology
  intro h
  rcases ρ with ⟨r, hr, c⟩
  have hc : T.supercuspidalClassRealPowerTwist r 1 c = c := by
    simpa only [PadicField.TopologicalData.CuspidalDatum.twist,
      PadicField.TopologicalData.CuspidalDatum.mk.injEq, heq_eq_eq, true_and] using h
  induction c using Quotient.inductionOn with
  | h A =>
    let At := SupercuspidalRep.twist (T.determinantPowerCharacter r 1)
      (T.isOpen_ker_determinantPowerCharacter r 1)
      (T.ker_determinant_le_ker_determinantPowerCharacter r 1) A
    change At.isoClass = A.isoClass at hc
    obtain ⟨e⟩ := (SupercuspidalRep.isoClass_eq_iff At A).mp hc
    let e' := SmoothRep.equivOfIso ((supercuspidalProperty (F := F.Carrier)
      (n := r)).ι.mapIso e.symm)
    exact one_ne_zero (exponent_eq_zero T r hr A.obj A.property.2.1 A.property.1 1 e')

end Langlands.Derivative.OrderedCuspidalProductTwistOne

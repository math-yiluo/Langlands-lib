import Langlands.AllFieldBZ.LocalField.Definitions
import Langlands.AllFieldBZ.Representation.Classification.SupercuspidalSupport
import Langlands.Representation.Derivative.OrderedCuspidalProductTwistOne

/-!
# All-field port of `Langlands.Representation.Derivative.OrderedCuspidalProductTwistOne`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.OrderedCuspidalProductTwistOne` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
namespace Langlands.AllFieldBZ.Derivative.OrderedCuspidalProductTwistOne
open Langlands.Derivative.OrderedCuspidalProductTwistOne hiding exponent_eq_zero twist_one_ne_self
open CategoryTheory
open Langlands.GeneralLinear
universe uF uV

variable {F : LocalFieldPackage.{uF}} (T : F.TopologicalData)

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
  let z := scalarToCenter (n := r) (Langlands.LocalFactor.LocalAbelian.uniformizerUnit T)
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
    (scalar (Langlands.LocalFactor.LocalAbelian.uniformizerUnit T)) : ℂ) = 1 at hv1
  rw [coe_realPowerCharacter, T.determinantNorm_scalar] at hv1
  simp only [Units.val_pow_eq_pow_val, NNReal.coe_pow,
    T.normalizedAbsUnits_coe, Langlands.LocalFactor.LocalAbelian.uniformizerUnit_coe,
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
    simpa only [LocalFieldPackage.TopologicalData.CuspidalDatum.twist,
      LocalFieldPackage.TopologicalData.CuspidalDatum.mk.injEq, heq_eq_eq, true_and] using h
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

end Langlands.AllFieldBZ.Derivative.OrderedCuspidalProductTwistOne

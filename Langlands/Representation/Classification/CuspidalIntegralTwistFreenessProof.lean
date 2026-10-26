import Langlands.Representation.Classification.CuspidalIntegralTwistFreenessStatement
import Langlands.Representation.Smooth.Schur.Proof
import Langlands.LocalField.Uniformizer

/-! Integral determinant twists cannot fix a positive-rank cuspidal class. -/

noncomputable section

namespace Langlands.Classification

open CategoryTheory GeneralLinear

universe uF uV uG

namespace IntegralTwistFreeness

/-- An equivalence with a scalar twist forces that character to be trivial
on the center of an irreducible admissible representation. -/
theorem character_eq_one_on_center
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (hρa : IsAdmissible ρ)
    (hρi : Representation.IsIrreducible ρ) (χ : G →* ℂˣ)
    (e : ρ.Equiv (twist χ ρ)) (z : Subgroup.center G) :
    χ z = 1 := by
  let := hρi
  let : Nontrivial V :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
  obtain ⟨ω, ⟨_, hω⟩, _⟩ := admissibleSchur_centralCharacter ρ hρa hρi
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hev : e v ≠ 0 := by
    intro h
    apply hv
    exact e.injective (by simpa using h)
  have he := Representation.IntertwiningMap.isIntertwining
    ρ (twist χ ρ) e.toIntertwiningMap (z : G) v
  change e (ρ (z : G) v) = (χ z : ℂ) • ρ (z : G) (e v) at he
  rw [hω, map_smul, hω, smul_smul] at he
  have hc : (ω z : ℂ) = (χ z : ℂ) * (ω z : ℂ) :=
    smul_left_injective ℂ hev he
  apply Units.ext
  exact mul_right_cancel₀ (ω z).ne_zero (by simpa using hc.symm)

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData)

/-- The scalar uniformizer measures the rank times the real exponent. -/
theorem scalar_uniformizer_value (r : ℕ) (s : ℝ) :
    (T.determinantPowerCharacter r s
      (scalar (LocalFactor.PadicAbelian.uniformizerUnit T)) : ℂ) =
      (((T.residueCardinality : ℝ) ^ (-(r : ℝ) * s) : ℝ) : ℂ) := by
  rw [coe_realPowerCharacter, T.determinantNorm_scalar]
  simp only [Units.val_pow_eq_pow_val, NNReal.coe_pow,
    T.normalizedAbsUnits_coe, LocalFactor.PadicAbelian.uniformizerUnit_coe,
    T.normalizedAbs_uniformizer, zpow_neg_one]
  have hq : 0 ≤ (T.residueCardinality : ℝ) := by positivity
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
    ← Real.rpow_neg_one, ← Real.rpow_mul hq]
  congr 2
  ring

/-- An actual irreducible admissible representation of positive rank cannot
be equivalent to a nontrivial real determinant twist of itself. -/
theorem exponent_eq_zero_of_equiv
    (r : ℕ) (hr : 0 < r)
    (A : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier))
    (hAa : letI := T.topology; A.IsAdmissible)
    (hAi : letI := T.topology; A.IsIrreducible) (s : ℝ)
    (e : letI := T.topology; A.representation.Equiv
      (twist (T.determinantPowerCharacter r s) A.representation)) :
    s = 0 := by
  let := T.topology
  let := T.generalLinearTopologicalGroup r
  have hc := character_eq_one_on_center A.representation hAa hAi
    (T.determinantPowerCharacter r s) e
    (scalarToCenter (LocalFactor.PadicAbelian.uniformizerUnit T))
  have hv := congrArg (fun a : ℂˣ => (a : ℂ)) hc
  change (T.determinantPowerCharacter r s
    (scalar (LocalFactor.PadicAbelian.uniformizerUnit T)) : ℂ) = 1 at hv
  rw [scalar_uniformizer_value] at hv
  have hq : 1 < (T.residueCardinality : ℝ) := by
    exact_mod_cast T.residueCardinality_gt_one
  have hexp : -(r : ℝ) * s = 0 :=
    (Real.rpow_right_inj (lt_trans zero_lt_one hq) (ne_of_gt hq)).mp
      (by simpa using Complex.ofReal_injective hv)
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  exact (mul_eq_zero.mp hexp).resolve_left (neg_ne_zero.mpr hr0)

end IntegralTwistFreeness

/-- The exact integral nonperiodicity statement for actual cuspidal data. -/
theorem cuspidalIntegralTwistFreeness
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    CuspidalIntegralTwistFreeness.{uF,uV} F T := by
  let := T.topology
  intro ρ k
  constructor
  · intro h
    rcases ρ with ⟨r, hr, c⟩
    have hc : T.supercuspidalClassRealPowerTwist r (k : ℝ) c = c := by
      simpa only [PadicField.TopologicalData.CuspidalDatum.twist,
        PadicField.TopologicalData.CuspidalDatum.mk.injEq, heq_eq_eq, true_and] using h
    have hs : (k : ℝ) = 0 := by
      induction c using Quotient.inductionOn with
      | h A =>
        let At := SupercuspidalRep.twist (T.determinantPowerCharacter r (k : ℝ))
          (T.isOpen_ker_determinantPowerCharacter r (k : ℝ))
          (T.ker_determinant_le_ker_determinantPowerCharacter r (k : ℝ)) A
        change At.isoClass = A.isoClass at hc
        obtain ⟨e⟩ := (SupercuspidalRep.isoClass_eq_iff At A).mp hc
        let e' := SmoothRep.equivOfIso ((supercuspidalProperty (F := F.Carrier)
          (n := r)).ι.mapIso e.symm)
        exact IntegralTwistFreeness.exponent_eq_zero_of_equiv T r hr A.obj
          A.property.2.1 A.property.1 (k : ℝ) e'
    exact_mod_cast hs
  · rintro rfl
    simp

end Langlands.Classification

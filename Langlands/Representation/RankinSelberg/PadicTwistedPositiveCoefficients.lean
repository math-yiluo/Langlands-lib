import Langlands.Representation.Whittaker.TwistedConjugatePair
import Langlands.Representation.Unitary.SupercuspidalRealUnitarizationProof
import Langlands.Representation.Twist.AdmissibilityProof
import Langlands.Representation.Category.Contragredient
import Langlands.Representation.RankinSelberg.AnalyticStatement
import Langlands.Representation.Shahidi.Induction

/-! # Positive normalized coefficient pairs at a contragredient twist -/

noncomputable section

namespace Langlands.RankinSelberg

open GeneralLinear HarmonicAnalysis Whittaker

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)

/-- A fixed inverse-standard functional gives weighted coefficient products
equal to squared norms on a unitarizable real determinant twist. -/
def HasPadicTwistedPositiveCoefficients
    (ψ : letI := T.topology; UnitaryAdditiveCharacter F.Carrier)
    (u : ℂ) (ℓ : letI := T.topology; glFunctionals ψ n π) : Prop :=
  letI := T.topology
  ∃ t : ℝ, IsUnitarizable (realPowerTwist (T.determinantNorm (n + 1)) t π) ∧
    ∃ m : glInverseFunctionals ψ n σ, m.val ≠ 0 ∧
      ∀ v : V, ∃ w : W, ∀ g : Langlands.GeneralLinear (n + 1) F.Carrier,
        determinantWeight (normalizedAbsoluteValue T) g (-u) *
            ((coefficientMap π ℓ v).val g * (coefficientMap σ m w).val g) =
          ((‖ℓ.val (realPowerTwist (T.determinantNorm (n + 1)) t π g v)‖ ^ 2 : ℝ) : ℂ)

/-- The actual normalized contragredient twist produces the positive
coefficient package from any supplied nonzero standard functional. -/
theorem hasPadicTwistedPositiveCoefficients_of_contragredient_twist
    (ψ : letI := T.topology; UnitaryAdditiveCharacter F.Carrier)
    (u : ℂ) (hπ : π.IsIrreducible) :
    letI := T.topology
    haveI := T.generalLinearTopologicalGroup (n + 1)
    IsSupercuspidal π → IsAdmissible σ →
      Nonempty ((Langlands.twist (T.determinantComplexPower (n + 1) (-u)) π).Equiv
        (smoothContragredient σ)) →
      ∀ ℓ : glFunctionals ψ n π, ℓ.val ≠ 0 →
        HasPadicTwistedPositiveCoefficients T π σ ψ u ℓ := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (n + 1)
  intro hπs hσ ⟨e⟩ ℓ hℓ
  obtain ⟨t, ⟨b⟩⟩ :=
    supercuspidalRealUnitarization p F T (n + 1) (by omega) V π hπ hπs
  let χ := T.determinantComplexPower (n + 1) (-u)
  let α := T.determinantPowerCharacter (n + 1) t
  have hdet (x : upperUnipotent (n + 1) F.Carrier) :
      determinant x.val = 1 := Units.ext (unipotent_det x)
  have hnorm (x : upperUnipotent (n + 1) F.Carrier) :
      T.determinantNorm (n + 1) x.val = 1 := by
    change T.normalizedAbsUnits (determinant x.val) = 1
    rw [hdet, map_one]
  have hχN : ∀ x : upperUnipotent (n + 1) F.Carrier, χ x.val = 1 := by
    intro x
    apply Units.ext
    rw [T.determinantComplexPower_apply, hnorm]
    simp
  have hαN : ∀ x : upperUnipotent (n + 1) F.Carrier, α x.val = 1 := by
    intro x
    apply Units.ext
    change (realPowerCharacter (T.determinantNorm (n + 1)) t x.val : ℂ) = 1
    rw [coe_realPowerCharacter, hnorm]
    simp
  have hτ : IsAdmissible (Langlands.twist α π) :=
    (isAdmissible_twist_iff α π
      (T.isOpen_ker_determinantPowerCharacter (n + 1) t)).mpr hπs.1
  obtain ⟨m, hm, hpair⟩ := exists_twisted_conjugate_functional χ α
    (T.isOpen_ker_determinantComplexPower (n + 1) (-u))
    (T.isOpen_ker_determinantPowerCharacter (n + 1) t)
    (GeneralLinear.compactOpen_cofinal F T (n + 1)) hσ e
    (upperUnipotent (n + 1) F.Carrier) (standardCharacter ψ n)
    hχN hαN (norm_standardCharacter ψ n) hτ b ℓ hℓ
  refine ⟨t, ⟨b⟩, m, hm, fun v => ?_⟩
  obtain ⟨w, hw⟩ := hpair v
  refine ⟨w, fun g => ?_⟩
  have hweight :
      determinantWeight (normalizedAbsoluteValue T) g (-u) = (χ g : ℂ) := by
    rw [T.determinantComplexPower_apply]
    rfl
  rw [hweight]
  erw [hw]
  simp only [← mul_assoc, mul_inv_cancel₀ (Units.ne_zero (χ g)), one_mul]
  rfl

/-- A nonzero first functional makes some paired product strictly positive at
the identity. This is a pointwise consequence of the squared-norm identity. -/
theorem HasPadicTwistedPositiveCoefficients.exists_identity_pos
    {ψ : letI := T.topology; UnitaryAdditiveCharacter F.Carrier}
    {u : ℂ} {ℓ : letI := T.topology; glFunctionals ψ n π}
    (h : HasPadicTwistedPositiveCoefficients T π σ ψ u ℓ)
    (hℓ : ℓ.val ≠ 0) :
    letI := T.topology
    ∃ m : glInverseFunctionals ψ n σ, m.val ≠ 0 ∧
      ∃ v : V, ∃ w : W,
        0 < ((coefficientMap π ℓ v).val 1 * (coefficientMap σ m w).val 1).re := by
  let := T.topology
  obtain ⟨t, _, m, hm, hpair⟩ := h
  obtain ⟨v, hv⟩ : ∃ v : V, ℓ.val v ≠ 0 := by
    by_contra h
    apply hℓ
    ext v
    exact not_not.mp (not_exists.mp h v)
  obtain ⟨w, hw⟩ := hpair v
  refine ⟨m, hm, v, w, ?_⟩
  have hnorm := hw 1
  simp only [determinantWeight, map_one, Units.val_one, Matrix.det_one, Complex.ofReal_one,
    Complex.one_cpow, one_mul, Module.End.one_apply] at hnorm
  rw [hnorm]
  change 0 < ‖ℓ.val v‖ ^ 2
  exact sq_pos_of_pos (norm_pos_iff.mpr hv)

end Langlands.RankinSelberg

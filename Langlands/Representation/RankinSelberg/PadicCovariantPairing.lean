import Langlands.Representation.RankinSelberg.TwistedPairingContragredient
import Langlands.Representation.RankinSelberg.AnalyticStatement
import Langlands.Representation.Category.Contragredient
import Langlands.Representation.Shahidi.Induction

/-! # The normalized p-adic specialization of covariant pairings -/

noncomputable section

namespace Langlands.RankinSelberg

open GeneralLinear

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)

/-- A nonzero pairing with the actual normalized determinant-weight covariance. -/
def HasNonzeroPadicCovariantPairing (u : ℂ) : Prop :=
  ∃ β : V →ₗ[ℂ] W →ₗ[ℂ] ℂ, β ≠ 0 ∧
    ∀ g v w, β (π g v) (σ g w) =
      determinantWeight (normalizedAbsoluteValue T) g u * β v w

/-- Normalized p-adic covariance has the inverse-power sign appearing in the
equal-rank supercuspidal target. The character is on the actual field units. -/
theorem HasNonzeroPadicCovariantPairing.exists_contragredient_equiv
    (u : ℂ) (hπ : π.IsIrreducible) (hσ : σ.IsIrreducible) :
    letI := T.topology
    haveI := T.generalLinearTopologicalGroup (n + 1)
    IsSmooth π → IsAdmissible σ →
    HasNonzeroPadicCovariantPairing T π σ u →
      ∃ χ : F.Carrierˣ →* ℂˣ,
        (∀ x : F.Carrierˣ,
          (χ x : ℂ) = ((T.normalizedAbs (x : F.Carrier) : ℝ) : ℂ) ^ (-u)) ∧
        Nonempty ((Langlands.twist (χ.comp determinant) π).Equiv
          (smoothContragredient σ)) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (n + 1)
  intro hπs hσa h
  let χ := Shahidi.complexPower T.normalizedAbsUnits (-u)
  have hchar : χ.comp determinant = (T.determinantComplexPower (n + 1) u)⁻¹ := by
    rw [← T.determinantComplexPower_neg,
      T.determinantComplexPower_eq_complexPower]
    rfl
  have hcov : HasNonzeroCovariantPairing π σ (T.determinantComplexPower (n + 1) u) := by
    obtain ⟨β, hβ, hcov⟩ := h
    refine ⟨β, hβ, fun g v w => ?_⟩
    rw [hcov, T.determinantComplexPower_apply]
    rfl
  refine ⟨χ, fun _ => rfl, ?_⟩
  rw [hchar]
  exact hcov.contragredient_equiv π σ _
    (GeneralLinear.compactOpen_cofinal F T (n + 1))
    hπ hσ hπs hσa (T.isOpen_ker_determinantComplexPower (n + 1) u)

end Langlands.RankinSelberg

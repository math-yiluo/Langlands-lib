import Langlands.Representation.Classification.TemperedExponentStatement

/-!
# Elementary edge cases for the tempered exponent criterion

The zero carrier and the recovery of a unitary central character from weak
exponent bounds are separated from the analytic estimates.
-/

namespace Langlands

universe uF uV

/-- A zero carrier is analytically tempered and has no Jacquet exponents. -/
def GLTemperedZeroCarrierStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V] [Subsingleton V]
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V),
    T.IsTempered ρ ∧
      ∀ (B : GeneralLinear.BlockShape n)
        (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ),
        ¬ T.IsJacquetExponent B ρ χ

/-- For a nonzero smooth representation with scalar central character, weak
Jacquet exponent bounds imply smoothness and unitarity of that character and
provide the actual central-character datum used by analytic temperedness. -/
def GLWeakExponentsUnitaryCentralCharacterStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (n : ℕ), 0 < n →
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V] [Nontrivial V]
      (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
      (ω : F.Carrierˣ →* ℂˣ),
      (letI := T.topology
       IsSmooth ρ) →
      (∀ (a : F.Carrierˣ) (v : V),
        ρ (GeneralLinear.scalar a) v = (ω a : ℂ) • v) →
      (∀ (B : GeneralLinear.BlockShape n)
        (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ),
        T.IsJacquetExponent B ρ χ →
        ∀ a : Fin B.length → F.Carrierˣ,
          Monotone (fun i => T.normalizedAbs (a i : F.Carrier)) →
          ‖(χ a : ℂ)‖ ≤ 1) →
      (letI := T.topology
       IsOpen (ω.ker : Set F.Carrierˣ) ∧
         (∀ a : F.Carrierˣ, ‖(ω a : ℂ)‖ = 1) ∧
         Nonempty (UnitaryCentralCharacter ρ))

/-- The two elementary reductions for the unchanged analytic exponent criterion.
This proposition asserts no coefficient or Haar-measure estimate. -/
def GLTemperedExponentEdgeStatement : Prop :=
  GLTemperedZeroCarrierStatement.{uF, uV} ∧
    GLWeakExponentsUnitaryCentralCharacterStatement.{uF, uV}

end Langlands

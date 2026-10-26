import Langlands.Representation.Classification.RelativeRegularComparisonStatement

/-! # Admissibility inputs for relative cosocle comparison -/

noncomputable section

namespace Langlands

open GeneralLinear RelativeRegularComparison

universe uF uV uW

/-- Analytic Levi admissibility and admissibility of every actual quotient of
an arbitrary real-twisted upper normalized induction. -/
def RelativeCosocleAdmissibilityStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ) (B : BlockShape n) (π : Rep.{uV} ℂ (B.Levi F.Carrier)),
      (IsLeviTempered T B π → IsAdmissible π.ρ) ∧
      (IsLeviSquareIntegrable T B π → IsAdmissible π.ρ) ∧
      (IsAdmissible π.ρ → ∀ t : Fin B.length → ℝ,
        let πt := Rep.of (T.leviRealPowerTwist B t π.ρ)
        let I := CuspidalJacquetMultiplicity.induced T B πt
        IsAdmissible πt.ρ ∧ IsAdmissible I.ρ ∧
        ∀ (J : Rep.{uW} ℂ (GeneralLinear n F.Carrier))
          (q : I.ρ.IntertwiningMap J.ρ), Function.Surjective q → IsAdmissible J.ρ)

end Langlands

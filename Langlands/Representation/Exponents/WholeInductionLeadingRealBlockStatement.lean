import Langlands.Representation.Classification.RelativeRegularComparisonStatement
import Langlands.Representation.Classification.ProductLeviCentralCharacter
import Langlands.Representation.Exponents.Central

/-! Actual inducing-layer retraction in the whole opposite Jacquet module. -/

noncomputable section

namespace Langlands.Exponents

open GeneralLinear RelativeRegularComparison

universe uF uV

/-- The inducing representation is a retract of its actual induced opposite
Jacquet module, and the resulting projector fixes every generalized full
central-character space with the inducing real parameter. -/
def WholeInductionLeadingRealBlockStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ (B : BlockShape n)
      (π : Rep.{uV} ℂ (B.Levi F.Carrier)),
      Representation.IsIrreducible π.ρ → IsLeviTempered T B π →
      ∀ (t : Fin B.length → ℝ), StrictAnti t →
        let πt := Rep.of (T.leviRealPowerTwist B t π.ρ)
        let X := CuspidalJacquetMultiplicity.induced T B πt
        let E := CuspidalJacquetMultiplicity.oppositeJacquet T B X
        ∃ (i : πt.ρ.IntertwiningMap E.ρ)
          (r : E.ρ.IntertwiningMap πt.ρ),
          (∀ v : πt, r (i v) = v) ∧
          ∀ (χ : Subgroup.center (B.Levi F.Carrier) →* ℂˣ),
            IsOpen (χ.ker : Set (Subgroup.center (B.Levi F.Carrier))) →
            T.IsRealPartOf (χ.comp (B.blockScalarToCenter F.Carrier))
              (fun k => (B.size k : ℝ) * t k) →
            ∀ v : E, v ∈ generalizedCentralCharacterSpace E.ρ χ →
              i (r v) = v

end Langlands.Exponents

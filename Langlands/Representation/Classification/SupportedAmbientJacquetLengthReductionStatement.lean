import Langlands.Representation.Classification.RelativeJacquetMultiplicityStatement
import Langlands.Representation.CuspidalSupport.NormalizedCuspidalInductionStatement

/-! A conditional finite-length reduction for a specified supported quotient. -/

noncomputable section

namespace Langlands

open GeneralLinear Geometric RelativeJacquetMultiplicity

universe uF uV uW

/-- Standard cuspidal induction length in one rank gives finite length and an
actual ambient Jacquet multiplicity for every specified supported quotient. -/
def GLSupportedAmbientJacquetLengthReductionStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n →
      CuspidalSupport.CuspidalInductionLengthTheorem.{uF, uV} F T n →
      ∀ (B : BlockShape n) (S : BlockRefinement B)
        (ω : Rep.{uV} ℂ ((B.flatten S).Levi F.Carrier)),
        Representation.IsIrreducible ω.ρ →
        CuspidalSupport.IsLeviCuspidal (B.flatten S) ω.ρ →
        ∀ (v₀ : Fin (B.flatten S).length → ℝ)
          (π : Rep.{uW} ℂ (B.Levi F.Carrier)),
          IsAdmissible π.ρ →
          (∃ q : (innerInduced T B S (fineTwist T B S ω v₀ 0)).ρ.IntertwiningMap π.ρ,
            Function.Surjective q) →
          ∀ t : Fin B.length → ℝ,
            let τ := fineTwist T B S ω v₀ t
            let πt := Rep.of (T.leviRealPowerTwist B t π.ρ)
            IsFiniteLength (MonoidAlgebra ℂ (GeneralLinear n F.Carrier))
                (CuspidalJacquetMultiplicity.induced T B πt).ρ.asModule ∧
              IsFiniteLength (MonoidAlgebra ℂ (refinedLevi F.Carrier B S))
                (ambientJacquet T B S πt).ρ.asModule ∧
              ∃ M : ℕ, HasJordanHolderMultiplicity (ambientJacquet T B S πt) τ M

end Langlands

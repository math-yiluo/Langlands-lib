import Langlands.Representation.Classification.RelativeJacquetMultiplicityStatement
import Langlands.Representation.Parabolic.OppositeRefinementFunctors

/-! # Algebraic lower bound for the actual relative Hom spaces

This module states the internal algebraic finite-dimensional lower bound
for the actual fine-to-opposite-Jacquet Hom spaces. It supplies no proof.
-/

noncomputable section

namespace Langlands

open GeneralLinear Geometric RelativeJacquetMultiplicity

universe uF uV uW uZ

/-- Both actual relative Hom spaces are finite dimensional, and the inner
dimension is bounded above by the outer dimension whenever the nontrivial
ambient representation is an actual quotient of the outer induction. -/
def FineRelativeHomLowerBoundStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ (B : BlockShape n) (S : BlockRefinement B)
      (ω : Rep.{uV} ℂ ((B.flatten S).Levi F.Carrier)),
      Representation.IsIrreducible ω.ρ →
      CuspidalSupport.IsLeviCuspidal (B.flatten S) ω.ρ →
      ∀ (v₀ : Fin (B.flatten S).length → ℝ)
        (π : Rep.{uW} ℂ (B.Levi F.Carrier)),
        Representation.IsIrreducible π.ρ → IsAdmissible π.ρ →
        ∀ (t : Fin B.length → ℝ) (J : Rep.{uZ} ℂ (GeneralLinear n F.Carrier)),
          Nontrivial J.V →
          (∃ q : (CuspidalJacquetMultiplicity.induced T B
            (Rep.of (T.leviRealPowerTwist B t π.ρ))).ρ.IntertwiningMap J.ρ,
            Function.Surjective q) →
          let Hout := (fineTwist T B S ω v₀ t).ρ.IntertwiningMap
            (T.normalizedComposedOppositeJacquet B S J.ρ)
          let Hin := (fineTwist T B S ω v₀ 0).ρ.IntertwiningMap
            (T.normalizedRefinedOppositeJacquet B S π.ρ)
          FiniteDimensional ℂ Hout ∧ FiniteDimensional ℂ Hin ∧
            Module.finrank ℂ Hin ≤ Module.finrank ℂ Hout

end Langlands

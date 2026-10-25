import Langlands.Representation.Classification.RelativeRecoveryStatement
import Langlands.Representation.Parabolic.OppositeRefinementFunctors

/-! J-specific finite Hom dimensions for the relative cosocle comparison. -/

noncomputable section

namespace Langlands

open GeneralLinear Geometric
open RelativeJacquetMultiplicity RelativeRegularComparison

universe uF uV uM uW uZ

/-- The actual fine cuspidal Hom spaces in the opposite Jacquet modules of
an arbitrary outer quotient and its tempered input are finite and equidimensional. -/
def GLRelativeCosocleHomComparisonStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ (B : BlockShape n) (Q : BlockRefinement B),
      let D := B.flatten Q
      ∀ (R : BlockRefinement D) (S : BlockRefinement B)
        (h : D.flatten R = B.flatten S)
        (ω : Rep.{uV} ℂ ((D.flatten R).Levi F.Carrier)),
        Representation.IsIrreducible ω.ρ →
        CuspidalSupport.IsLeviCuspidal (D.flatten R) ω.ρ →
        IsUnitarizable ω.ρ →
        ∀ v₀ : Fin (D.flatten R).length → ℝ,
          IsPositiveRootParameter D R v₀ →
          let ωB : Rep.{uV} ℂ ((B.flatten S).Levi F.Carrier) := h ▸ ω
          let vB : Fin (B.flatten S).length → ℝ := h ▸ v₀
          ∀ σ : Rep.{uM} ℂ (D.Levi F.Carrier),
            Representation.IsIrreducible σ.ρ → IsLeviSquareIntegrable T D σ →
            (∃ q : (innerInduced T D R (fineTwist T D R ω v₀ 0)).ρ.IntertwiningMap σ.ρ,
              Function.Surjective q) →
            ∀ π : Rep.{uW} ℂ (B.Levi F.Carrier),
              Representation.IsIrreducible π.ρ → IsLeviTempered T B π →
              ∀ t : Fin B.length → ℝ, StrictAnti t →
                let πt := Rep.of (T.leviRealPowerTwist B t π.ρ)
                ∀ J : Rep.{uZ} ℂ (GeneralLinear n F.Carrier),
                  Representation.IsIrreducible J.ρ →
                  (∃ q : (CuspidalJacquetMultiplicity.induced T B πt).ρ.IntertwiningMap J.ρ,
                    Function.Surjective q) →
                  let τ₀ := fineTwist T B S ωB vB 0
                  let τt := fineTwist T B S ωB vB t
                  let Hout := τt.ρ.IntertwiningMap
                    (T.normalizedComposedOppositeJacquet B S J.ρ)
                  let Hin := τ₀.ρ.IntertwiningMap
                    (T.normalizedRefinedOppositeJacquet B S π.ρ)
                  FiniteDimensional ℂ Hout ∧ FiniteDimensional ℂ Hin ∧
                    Module.finrank ℂ Hout = Module.finrank ℂ Hin

end Langlands

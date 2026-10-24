import Langlands.Representation.Classification.RelativeRecoveryStatement

/-!
# Relative cosocle multiplicities

The GL_n form of Silberger 1978, Proposition 5.9, on the actual canonical
radical quotients already constructed as `Classification.head`.
-/

noncomputable section

namespace Langlands

open GeneralLinear Geometric
open RelativeJacquetMultiplicity RelativeRegularComparison

universe uF uV uM uW uZ

/-- The multiplicity of an arbitrary tempered coarse representation in the
inner cosocle equals that of its regular-positive outer quotient in the fine
ambient cosocle. No inner support premise is imposed on the coarse input. -/
def GLRelativeCosocleMultiplicityStatement : Prop :=
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
                  ∃ m : ℕ,
                    HasJordanHolderMultiplicity
                      (Rep.of (Classification.head
                        (RelativeRecovery.fineAmbientInduced T B S ωB vB t).ρ)) J m ∧
                    HasJordanHolderMultiplicity
                      (Rep.of (Classification.head
                        (innerInduced T B S (fineTwist T B S ωB vB 0)).ρ)) π m

end Langlands

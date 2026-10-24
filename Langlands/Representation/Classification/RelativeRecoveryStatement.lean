import Langlands.Representation.Classification.RelativeRegularComparisonStatement

/-!
# Relative recovery of inducing representations

Supported recovery and arbitrary-tempered quotient reflection, corresponding
to Silberger 1978, Propositions 5.7 and 5.8.
-/

noncomputable section

namespace Langlands

open GeneralLinear Geometric
open RelativeJacquetMultiplicity RelativeRegularComparison

universe uF uV uM uW uX uZ

namespace RelativeRecovery

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)

/-- Actual ambient induction from the fine flat product Levi, with the same
negative fine and restricted positive coarse real twist as `fineTwist`. -/
def fineAmbientInduced (ω : Rep.{uV} ℂ ((B.flatten S).Levi F.Carrier))
    (v₀ : Fin (B.flatten S).length → ℝ) (t : Fin B.length → ℝ) :
    Rep.{max uF uV} ℂ (GeneralLinear n F.Carrier) :=
  CuspidalJacquetMultiplicity.induced T (B.flatten S)
    (Rep.of (T.leviRealPowerTwist (B.flatten S)
      (fun k => -v₀ k + t ((B.flattenBlockEquiv S).symm k).1) ω.ρ))

end RelativeRecovery

/-- A common outer irreducible quotient recovers the supported tempered coarse
representation even when the competing fine-supported quotient is not tempered. -/
def GLSupportedRelativeRecoveryStatement : Prop :=
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
              (∃ q : (middleInduced T B Q σ).ρ.IntertwiningMap π.ρ,
                Function.Surjective q) →
              (∃ q : (innerInduced T B S (fineTwist T B S ωB vB 0)).ρ.IntertwiningMap π.ρ,
                Function.Surjective q) →
              ∀ θ : Rep.{uX} ℂ (B.Levi F.Carrier),
                Representation.IsIrreducible θ.ρ → IsAdmissible θ.ρ →
                (∃ q : (innerInduced T B S (fineTwist T B S ωB vB 0)).ρ.IntertwiningMap θ.ρ,
                  Function.Surjective q) →
                ∀ t : Fin B.length → ℝ, StrictAnti t →
                  let πt := Rep.of (T.leviRealPowerTwist B t π.ρ)
                  let θt := Rep.of (T.leviRealPowerTwist B t θ.ρ)
                  ∀ J : Rep.{uZ} ℂ (GeneralLinear n F.Carrier),
                    Representation.IsIrreducible J.ρ →
                    (∃ q : (CuspidalJacquetMultiplicity.induced T B πt).ρ.IntertwiningMap J.ρ,
                      Function.Surjective q) →
                    (∃ q : (CuspidalJacquetMultiplicity.induced T B θt).ρ.IntertwiningMap J.ρ,
                      Function.Surjective q) →
                    Nonempty (π.ρ.Equiv θ.ρ)

/-- For arbitrary tempered coarse input, a common irreducible quotient of its
outer induction and the specified fine ambient induction forces an inner quotient.
The coarse input has no assumed middle or fine support map. -/
def GLTemperedRelativeQuotientReflectionStatement : Prop :=
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
                  (∃ q : (RelativeRecovery.fineAmbientInduced T B S ωB vB t).ρ.IntertwiningMap J.ρ,
                    Function.Surjective q) →
                  ∃ q : (innerInduced T B S (fineTwist T B S ωB vB 0)).ρ.IntertwiningMap π.ρ,
                    Function.Surjective q

/-- The two relative recovery assertions, with their different support scopes. -/
def GLRelativeRecoveryStatement : Prop :=
  GLSupportedRelativeRecoveryStatement.{uF, uV, uM, uW, uX, uZ} ∧
    GLTemperedRelativeQuotientReflectionStatement.{uF, uV, uM, uW, uZ}

end Langlands

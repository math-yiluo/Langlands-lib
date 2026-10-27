import Langlands.Representation.Classification.RelativeRecoveryStatement
import Langlands.Representation.Parabolic.SecondAdjointnessStatement

/-! Conditional detection of actual fine induction quotients by nonzero
intertwiners into the actual normalized refined and composed opposite Jacquet
modules. The two second-adjointness clauses are explicit premises. -/

noncomputable section

namespace Langlands

open GeneralLinear Geometric

universe uF uV uW uZ

/-- Assuming the standard and refined second-adjointness clauses, a nonzero
intertwiner from the actual fine twist into the normalized refined, or
composed, opposite Jacquet module of an admissible irreducible target exists
exactly when the matching actual inner, or ambient fine, induction has a
surjective intertwiner onto that target. -/
def FineOppositeJacquetQuotientDetectionStatement : Prop :=
  Parabolic.StandardSecondAdjointnessClause.{uF, uV, uZ} →
  Parabolic.RefinedSecondAdjointnessClause.{uF, uV, uW} →
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ (B : BlockShape n) (S : BlockRefinement B)
      (ω : Rep.{uV} ℂ ((B.flatten S).Levi F.Carrier)),
      Representation.IsIrreducible ω.ρ →
      CuspidalSupport.IsLeviCuspidal (B.flatten S) ω.ρ →
      ∀ (v : Fin (B.flatten S).length → ℝ) (t : Fin B.length → ℝ),
        let τ := RelativeJacquetMultiplicity.fineTwist T B S ω v t
        (∀ π : Rep.{uW} ℂ (B.Levi F.Carrier), IsAdmissible π.ρ →
          Representation.IsIrreducible π.ρ →
          ((∃ f : τ.ρ.IntertwiningMap
            (T.normalizedRefinedOppositeJacquet B S π.ρ), f ≠ 0) ↔
            ∃ q : (RelativeJacquetMultiplicity.innerInduced T B S τ).ρ.IntertwiningMap
              π.ρ, Function.Surjective q)) ∧
        (∀ J : Rep.{uZ} ℂ (GeneralLinear n F.Carrier), IsAdmissible J.ρ →
          Representation.IsIrreducible J.ρ →
          ((∃ f : τ.ρ.IntertwiningMap
            (T.normalizedComposedOppositeJacquet B S J.ρ), f ≠ 0) ↔
            ∃ q : (RelativeRecovery.fineAmbientInduced T B S ω v t).ρ.IntertwiningMap
              J.ρ, Function.Surjective q))

end Langlands

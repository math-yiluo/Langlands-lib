import Langlands.Representation.Classification.RelativeRegularComparisonStatement

/-!
# Joint fine, middle and coarse support of tempered product-Levi representations

The common existence prerequisite for the supported relative comparison and
recovery statements, derived from Silberger 1978, pp.98–99. This is a proposition
definition, not a proof.
-/

namespace Langlands

open GeneralLinear Geometric

universe uF uV

/-- Every irreducible analytically tempered product-Levi representation admits
joint unitary cuspidal and discrete-series support, with actual surjections
from the fine induction to the middle representation and from both middle
and fine inductions to the given coarse representation. -/
def GLTemperedJointSupportStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ (B : BlockShape n)
      (π : Rep.{uV} ℂ (B.Levi F.Carrier)),
      Representation.IsIrreducible π.ρ →
      RelativeRegularComparison.IsLeviTempered T B π →
      ∃ Q : BlockRefinement B,
        let D := B.flatten Q
        ∃ (R : BlockRefinement D) (S : BlockRefinement B)
          (h : D.flatten R = B.flatten S)
          (ω : Rep.{max uF uV} ℂ ((D.flatten R).Levi F.Carrier))
          (v₀ : Fin (D.flatten R).length → ℝ)
          (σ : Rep.{max uF uV} ℂ (D.Levi F.Carrier)),
          Representation.IsIrreducible ω.ρ ∧
          CuspidalSupport.IsLeviCuspidal (D.flatten R) ω.ρ ∧
          IsUnitarizable ω.ρ ∧
          RelativeRegularComparison.IsPositiveRootParameter D R v₀ ∧
          Representation.IsIrreducible σ.ρ ∧
          RelativeRegularComparison.IsLeviSquareIntegrable T D σ ∧
          ∃ (qFineMiddle : (RelativeJacquetMultiplicity.innerInduced T D R
              (RelativeJacquetMultiplicity.fineTwist T D R ω v₀ 0)).ρ.IntertwiningMap σ.ρ)
            (qMiddleCoarse : (RelativeRegularComparison.middleInduced T B Q σ).ρ.IntertwiningMap π.ρ)
            (qFineCoarse : (RelativeJacquetMultiplicity.innerInduced T B S
              (RelativeJacquetMultiplicity.fineTwist T B S
                (h ▸ ω) (h ▸ v₀) 0)).ρ.IntertwiningMap π.ρ),
            Function.Surjective qFineMiddle ∧
            Function.Surjective qMiddleCoarse ∧
            Function.Surjective qFineCoarse

end Langlands

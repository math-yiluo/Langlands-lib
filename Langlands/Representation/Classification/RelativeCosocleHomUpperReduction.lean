import Langlands.Representation.Classification.FineRelativeHomLowerBoundProof
import Langlands.Representation.Classification.RelativeCosocleHomComparisonStatement

noncomputable section

namespace Langlands.RelativeCosocleHomUpperReduction

open GeneralLinear Geometric
open RelativeJacquetMultiplicity RelativeRegularComparison

universe uF uV uM uW uZ

-- The shape-equality transport follows Worker 435's shared assembly draft.
private theorem transportFineData {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
    (T : F.TopologicalData) {n : ℕ} {C D : BlockShape n} (h : C = D)
    (ω : Rep.{uV} ℂ (C.Levi F.Carrier)) :
    letI := T.topology
    Representation.IsIrreducible ω.ρ → CuspidalSupport.IsLeviCuspidal C ω.ρ →
      Representation.IsIrreducible (h ▸ ω : Rep ℂ (D.Levi F.Carrier)).ρ ∧
        CuspidalSupport.IsLeviCuspidal D (h ▸ ω : Rep ℂ (D.Levi F.Carrier)).ρ := by
  cases h
  exact fun hi hc => ⟨hi, hc⟩

/-- The upper finrank inequality, with the entire exact parent
setup and all five independent universes. -/
def UpperBoundCase : Prop :=
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
                  Module.finrank ℂ Hout ≤ Module.finrank ℂ Hin

set_option maxHeartbeats 800000 in
/-- The upper inequality and the finite-dimensional algebraic lower bound
imply the exact comparison proposition. -/
theorem comparisonOfUpperBound
    (hupper : UpperBoundCase.{uF, uV, uM, uW, uZ}) :
    GLRelativeCosocleHomComparisonStatement.{uF, uV, uM, uW, uZ} := by
  dsimp only [GLRelativeCosocleHomComparisonStatement]
  intro p _ F T
  let := T.topology
  intro n hn B Q R S h ω hωirr hωcusp hωunit v₀ hv₀ σ hσirr hσdisc hσquot
    π hπirr hπtemp t ht J hJirr hJquot
  let ωB : Rep.{uV} ℂ ((B.flatten S).Levi F.Carrier) := h ▸ ω
  let vB : Fin (B.flatten S).length → ℝ := h ▸ v₀
  obtain ⟨hωBirr, hωBcusp⟩ := transportFineData T h ω hωirr hωcusp
  let := hJirr
  have hJnontriv : Nontrivial J.V :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GeneralLinear n F.Carrier)) J.ρ.asModule
  have hfinite := fineRelativeHomLowerBound
    p F T n hn B S ωB hωBirr hωBcusp vB π hπirr hπtemp.isAdmissible t J
      hJnontriv hJquot
  have hle := hupper p F T n hn B Q R S h ω hωirr hωcusp hωunit v₀ hv₀
    σ hσirr hσdisc hσquot π hπirr hπtemp t ht J hJirr hJquot
  exact ⟨hfinite.1, hfinite.2.1, Nat.le_antisymm hle hfinite.2.2⟩

end Langlands.RelativeCosocleHomUpperReduction

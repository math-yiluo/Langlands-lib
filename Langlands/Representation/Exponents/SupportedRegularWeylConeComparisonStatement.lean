import Langlands.Representation.Classification.RelativeRegularComparisonStatement
import Langlands.Representation.Exponents.ComplexTwistFamilies
import Langlands.Representation.Exponents.Chambers

/-!
# Two-sided Weyl and cone comparison for supported regular data

An internal GL_n statement extracted from the parameter comparison in
Silberger 1978, Proposition 6.1, before numerical rigidity and tempered-class
recovery. No comparison or continuation conclusion is assumed as input.
-/

noncomputable section

namespace Langlands

open GeneralLinear Geometric
open RelativeJacquetMultiplicity RelativeRegularComparison

universe uF uV1 uV2 uM1 uM2 uW1 uW2 uJ

/-- Two independently supported regular standard modules with a common
irreducible quotient admit one actual fine-support Weyl comparison satisfying
the fixed real-parameter relation and both transported tempered-cone bounds. -/
def GLSupportedRegularWeylConeComparisonStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n →
      ∀ (B1 : BlockShape n) (Q1 : BlockRefinement B1),
        let D1 := B1.flatten Q1
        ∀ (R1 : BlockRefinement D1) (S1 : BlockRefinement B1)
          (h1 : D1.flatten R1 = B1.flatten S1)
          (ω1 : Rep.{uV1} ℂ ((D1.flatten R1).Levi F.Carrier)),
          Representation.IsIrreducible ω1.ρ →
          CuspidalSupport.IsLeviCuspidal (D1.flatten R1) ω1.ρ →
          IsUnitarizable ω1.ρ →
          ∀ v1 : Fin (D1.flatten R1).length → ℝ,
            IsPositiveRootParameter D1 R1 v1 →
            let ωB1 : Rep.{uV1} ℂ ((B1.flatten S1).Levi F.Carrier) := h1 ▸ ω1
            let vB1 : Fin (B1.flatten S1).length → ℝ := h1 ▸ v1
            ∀ σ1 : Rep.{uM1} ℂ (D1.Levi F.Carrier),
              Representation.IsIrreducible σ1.ρ → IsLeviSquareIntegrable T D1 σ1 →
              (∃ q : (innerInduced T D1 R1 (fineTwist T D1 R1 ω1 v1 0)).ρ.IntertwiningMap
                  σ1.ρ, Function.Surjective q) →
              ∀ π1 : Rep.{uW1} ℂ (B1.Levi F.Carrier),
                Representation.IsIrreducible π1.ρ → IsLeviTempered T B1 π1 →
                (∃ q : (middleInduced T B1 Q1 σ1).ρ.IntertwiningMap π1.ρ,
                  Function.Surjective q) →
                (∃ q : (innerInduced T B1 S1 (fineTwist T B1 S1 ωB1 vB1 0)).ρ.IntertwiningMap
                    π1.ρ, Function.Surjective q) →
                ∀ t1 : Fin B1.length → ℝ, StrictAnti t1 →
                  ∀ (B2 : BlockShape n) (Q2 : BlockRefinement B2),
                    let D2 := B2.flatten Q2
                    ∀ (R2 : BlockRefinement D2) (S2 : BlockRefinement B2)
                      (h2 : D2.flatten R2 = B2.flatten S2)
                      (ω2 : Rep.{uV2} ℂ ((D2.flatten R2).Levi F.Carrier)),
                      Representation.IsIrreducible ω2.ρ →
                      CuspidalSupport.IsLeviCuspidal (D2.flatten R2) ω2.ρ →
                      IsUnitarizable ω2.ρ →
                      ∀ v2 : Fin (D2.flatten R2).length → ℝ,
                        IsPositiveRootParameter D2 R2 v2 →
                        let ωB2 : Rep.{uV2} ℂ ((B2.flatten S2).Levi F.Carrier) := h2 ▸ ω2
                        let vB2 : Fin (B2.flatten S2).length → ℝ := h2 ▸ v2
                        ∀ σ2 : Rep.{uM2} ℂ (D2.Levi F.Carrier),
                          Representation.IsIrreducible σ2.ρ →
                          IsLeviSquareIntegrable T D2 σ2 →
                          (∃ q : (innerInduced T D2 R2
                              (fineTwist T D2 R2 ω2 v2 0)).ρ.IntertwiningMap σ2.ρ,
                            Function.Surjective q) →
                          ∀ π2 : Rep.{uW2} ℂ (B2.Levi F.Carrier),
                            Representation.IsIrreducible π2.ρ → IsLeviTempered T B2 π2 →
                            (∃ q : (middleInduced T B2 Q2 σ2).ρ.IntertwiningMap π2.ρ,
                              Function.Surjective q) →
                            (∃ q : (innerInduced T B2 S2
                                (fineTwist T B2 S2 ωB2 vB2 0)).ρ.IntertwiningMap π2.ρ,
                              Function.Surjective q) →
                            ∀ t2 : Fin B2.length → ℝ, StrictAnti t2 →
                              ∀ J : Rep.{uJ} ℂ (GeneralLinear n F.Carrier),
                                Representation.IsIrreducible J.ρ →
                                (∃ q : (CuspidalJacquetMultiplicity.induced T B1
                                    (Rep.of (T.leviRealPowerTwist B1 t1 π1.ρ))).ρ.IntertwiningMap
                                    J.ρ, Function.Surjective q) →
                                (∃ q : (CuspidalJacquetMultiplicity.induced T B2
                                    (Rep.of (T.leviRealPowerTwist B2 t2 π2.ρ))).ρ.IntertwiningMap
                                    J.ρ, Function.Surjective q) →
                                let C1 := B1.flatten S1
                                let C2 := B2.flatten S2
                                let V1 : Fin n → ℝ := fun a => vB1 (blockIndex C1 a)
                                let V2 : Fin n → ℝ := fun a => vB2 (blockIndex C2 a)
                                let A1 : Fin n → ℝ := fun a => t1 (blockIndex B1 a)
                                let A2 : Fin n → ℝ := fun a => t2 (blockIndex B2 a)
                                ∃ (w : Equiv.Perm (Fin n))
                                  (hw : CuspidalSupport.ConjugatesLevi
                                    (F := F.Carrier) C1 C2 w),
                                  Nonempty (@Representation.Equiv ℂ (C2.Levi F.Carrier)
                                    ωB1.V ωB2.V _ _
                                    ωB1.hV1.toAddCommMonoid ωB2.hV1.toAddCommMonoid
                                    ωB1.hV2 ωB2.hV2
                                    (@CuspidalSupport.transport F.Carrier _ n C1 C2
                                      ωB1.V ωB1.hV1 ωB1.hV2 w hw
                                    (@PadicField.TopologicalData.leviRealPowerTwist
                                      p _ F T n C1 ωB1.V ωB1.hV1 ωB1.hV2
                                      (RealTwistFamilies.nestedParameter B1 S1 vB1 t1)
                                      ωB1.ρ))
                                    (@PadicField.TopologicalData.leviRealPowerTwist
                                      p _ F T n C2 ωB2.V ωB2.hV1 ωB2.hV2
                                      (RealTwistFamilies.nestedParameter B2 S2 vB2 t2)
                                      ωB2.ρ)) ∧
                                  (∀ a : Fin n,
                                    V1 (w.symm a) - A1 (w.symm a) = V2 a - A2 a) ∧
                                  Exponents.IsClosedPositiveRootCone
                                    (fun a => V1 (w.symm a)) ∧
                                  Exponents.IsClosedPositiveRootCone
                                    (fun a => V2 (w a))

end Langlands

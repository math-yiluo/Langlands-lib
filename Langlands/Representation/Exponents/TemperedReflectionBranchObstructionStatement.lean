import Langlands.Representation.Classification.RelativeRecoveryStatement
import Langlands.Representation.Exponents.ComplexTwistFamilies

/-!
# A selected Weyl-branch obstruction for tempered quotient reflection

An internal, source-derived statement boundary in the continuation argument of
Silberger 1978, Proposition 5.8, printed p.102. This file states the selected
branch and its zero-parameter class occurrence; it contains no proof of them.
-/

noncomputable section

namespace Langlands

open GeneralLinear Geometric
open RelativeJacquetMultiplicity RelativeRegularComparison

universe uF uV uM uW uZ

/-- If an arbitrary tempered coarse input has the two specified surjections to
one irreducible ambient quotient but no fine-to-coarse quotient, one actual
fine-Levi-conjugating permutation outside the coarse Weyl group fixes the real
parameter difference and supplies the transported negative fine twist as a
class exponent of the entire untwisted outer induction. -/
def GLTemperedReflectionBranchObstructionStatement : Prop :=
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
                  (¬ ∃ q : (innerInduced T B S (fineTwist T B S ωB vB 0)).ρ.IntertwiningMap π.ρ,
                    Function.Surjective q) →
                  let C := B.flatten S
                  ∃ w : Equiv.Perm (Fin n),
                    ∃ hw : CuspidalSupport.ConjugatesLevi (F := F.Carrier) C C w,
                      w ∉ Geometric.blockWeyl B ∧
                      (∀ a : Fin n,
                        vB (Geometric.blockIndex C (w.symm a)) -
                            t (Geometric.blockIndex B (w.symm a)) =
                          vB (Geometric.blockIndex C a) -
                            t (Geometric.blockIndex B a)) ∧
                      T.IsOppositeJacquetClassExponent C
                        (CuspidalJacquetMultiplicity.induced T B π)
                        (@Rep.of ℂ (C.Levi F.Carrier) _ _ ωB.V ωB.hV1 ωB.hV2
                          (@CuspidalSupport.transport F.Carrier _ n C C ωB.V ωB.hV1 ωB.hV2 w hw
                            (@PadicField.TopologicalData.leviRealPowerTwist
                              p _ F T n C ωB.V ωB.hV1 ωB.hV2 (-vB) ωB.ρ)))

end Langlands

import Langlands.Group.GL.NestedRefinement
import Langlands.Representation.Classification.RelativeRegularComparisonStatement

/-!
# Normalized induction in stages inside a product Levi

The actual composite refinement determines both the fine shape transport and
the direct induction. These proposition definitions include the comparison's
evaluation formulas and its surjective-quotient transport consequence.
-/

noncomputable section

namespace Langlands

universe uF uV uM uW

namespace NestedInduction

open GeneralLinear Geometric RelativeRegularComparison RelativeJacquetMultiplicity

set_option maxHeartbeats 800000

/-- Comparison of the constructed smooth parts for arbitrary fine input,
with evaluation at the middle identity and the inverse half-modulus formula. -/
def Comparison : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ) (B : BlockShape n) (Q : BlockRefinement B),
      let D := B.flatten Q
      ∀ (R : BlockRefinement D) (V : Type uV) [AddCommGroup V] [Module ℂ V]
        (ω : Representation ℂ ((D.flatten R).Levi F.Carrier) V),
        let S := B.composeRefinement Q R
        let h := B.flatten_composeRefinement Q R
        let ωB : Representation ℂ ((B.flatten S).Levi F.Carrier) V := h ▸ ω
        let A := middleInduced T B Q (middleInduced T D R (Rep.of ω))
        let C := middleInduced T B S (Rep.of ωB)
        ∃ E : A.ρ.Equiv C.ρ,
          (∀ (f : A) (g : B.Levi F.Carrier),
            Induction.eval _ _ (E f) g =
              Induction.eval _ _ (Induction.eval _ _ f g) 1) ∧
          (∀ (f : C) (g : B.Levi F.Carrier) (m : D.Levi F.Carrier),
            Induction.eval _ _ (Induction.eval _ _ (E.symm f) g) m =
              (T.refinedLeviHalfModulus B Q
                (flattenedLeviEquiv F.Carrier B Q m) : ℂ)⁻¹ •
                Induction.eval _ _ f
                  ((flattenedLeviEquiv F.Carrier B Q m).val * g))

/-- Surjective fine-to-middle and induced-middle-to-coarse intertwiners yield
a fine-to-coarse surjection with both fine data transported by the actual
ordered shape equality and with zero outer twist. -/
def QuotientTransport : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ) (B : BlockShape n) (Q : BlockRefinement B),
      let D := B.flatten Q
      ∀ (R : BlockRefinement D)
        (ω : Rep.{uV} ℂ ((D.flatten R).Levi F.Carrier))
        (v₀ : Fin (D.flatten R).length → ℝ)
        (σ : Rep.{uM} ℂ (D.Levi F.Carrier))
        (π : Rep.{uW} ℂ (B.Levi F.Carrier))
        (qFineMiddle :
          (innerInduced T D R (fineTwist T D R ω v₀ 0)).ρ.IntertwiningMap σ.ρ)
        (qMiddleCoarse : (middleInduced T B Q σ).ρ.IntertwiningMap π.ρ),
        Function.Surjective qFineMiddle →
        Function.Surjective qMiddleCoarse →
        let S := B.composeRefinement Q R
        let h := B.flatten_composeRefinement Q R
        ∃ qFineCoarse :
          (innerInduced T B S
            (fineTwist T B S (h ▸ ω) (h ▸ v₀) 0)).ρ.IntertwiningMap π.ρ,
          Function.Surjective qFineCoarse

end NestedInduction

/-- Normalized nested product-Levi induction comparison and its algebraic
surjective-quotient transport consequence. -/
def NormalizedNestedInductionStatement : Prop :=
  NestedInduction.Comparison.{uF, uV} ∧
    NestedInduction.QuotientTransport.{uF, uV, uM, uW}

end Langlands

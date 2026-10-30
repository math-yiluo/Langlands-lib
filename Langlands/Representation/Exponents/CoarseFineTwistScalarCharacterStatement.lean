import Langlands.Representation.Exponents.UnitaryFineTwistScalarCharacterStatement
import Langlands.Representation.Exponents.PositiveRootBlockSumsStatement

/-! The coarse scalar character of the actual nested fine determinant twist. -/

namespace Langlands.Exponents

open GeneralLinear Geometric RelativeJacquetMultiplicity RelativeRegularComparison

universe uF uV

/-- Restricting a nested positive-root fine twist to the coarse block scalars
gives an open-kernel character with the size-weighted coarse real part. -/
def CoarseFineTwistScalarCharacterStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ) (B : BlockShape n) (Q : BlockRefinement B)
      (R : BlockRefinement (B.flatten Q)) (S : BlockRefinement B)
      (h : (B.flatten Q).flatten R = B.flatten S)
      (ω : Rep.{uV} ℂ (((B.flatten Q).flatten R).Levi F.Carrier)),
      Representation.IsIrreducible ω.ρ → IsAdmissible ω.ρ → IsUnitarizable ω.ρ →
      ∀ (v₀ : Fin ((B.flatten Q).flatten R).length → ℝ),
        IsPositiveRootParameter (B.flatten Q) R v₀ →
        let ωB : Rep.{uV} ℂ ((B.flatten S).Levi F.Carrier) := h ▸ ω
        let vB : Fin (B.flatten S).length → ℝ := h ▸ v₀
        ∀ (t : Fin B.length → ℝ),
          ∃ χ : (Fin B.length → F.Carrierˣ) →* ℂˣ,
            IsOpen (χ.ker : Set (Fin B.length → F.Carrierˣ)) ∧
            (∀ (a : Fin B.length → F.Carrierˣ) (w : ωB),
              (fineTwist T B S ωB vB t).ρ
                (flattenedLeviEquiv F.Carrier B S
                  ((B.flatten S).blockScalarLevi F.Carrier
                    (fun k => a ((B.flattenBlockEquiv S).symm k).1))) w =
                (χ a : ℂ) • w) ∧
            T.IsRealPartOf χ (fun i => (B.size i : ℝ) * t i)

end Langlands.Exponents

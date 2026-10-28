import Langlands.Representation.Classification.RelativeJacquetMultiplicityStatement
import Langlands.Representation.Classification.RelativeGenericWeylCountStatement

/-!
# Equal actual Jacquet totals for generic fine cuspidal induction

The two full opposite-Jacquet modules have actual finite composition-series
counts given by the same fine-twist self-association cardinality.
This is a derived proposition definition; its proof is separate.
-/

noncomputable section

namespace Langlands

open GeneralLinear Geometric RelativeJacquetMultiplicity

universe uF uV

/-- For the actual full inner induction of relatively generic fine cuspidal
data, both full opposite-Jacquet modules have the stated finite count of the
fine twist. Each conjunct includes an actual finite composition series. -/
def GLRelativeGenericJacquetTotalsStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ (B : BlockShape n) (S : BlockRefinement B)
      (ω : Rep.{uV} ℂ ((B.flatten S).Levi F.Carrier)),
      Representation.IsIrreducible ω.ρ →
      CuspidalSupport.IsLeviCuspidal (B.flatten S) ω.ρ → IsUnitarizable ω.ρ →
      ∀ (v₀ : Fin (B.flatten S).length → ℝ) (t : Fin B.length → ℝ),
        IsRelativeGenericParameter (B.flatten S) B v₀ t →
        let C := B.flatten S
        let σ := T.leviRealPowerTwist C
          (fun k => -v₀ k + t ((B.flattenBlockEquiv S).symm k).1) ω.ρ
        let τ := fineTwist T B S ω v₀ t
        let I := innerInduced T B S τ
        let N := Nat.card (CuspidalSupport.AssociatingPermutations C C σ σ)
        HasJordanHolderMultiplicity (innerJacquet T B S I) τ N ∧
          HasJordanHolderMultiplicity (ambientJacquet T B S I) τ N

end Langlands

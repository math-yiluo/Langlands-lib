import Langlands.Representation.Classification.RelativeJacquetMultiplicityStatement

/-! Regularity of actual real twists on product Levis and the fine subgroup. -/

noncomputable section

namespace Langlands

open GeneralLinear Geometric

universe uF uV

/-- Arbitrary real determinant twists preserve actual product-Levi cuspidality. -/
def LeviRealPowerCuspidalityStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ) (B : BlockShape n) (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (B.Levi F.Carrier) V) (s : Fin B.length → ℝ),
      CuspidalSupport.IsLeviCuspidal B (T.leviRealPowerTwist B s ρ) ↔
        CuspidalSupport.IsLeviCuspidal B ρ

/-- Arbitrary real determinant twists preserve admissibility. -/
def LeviRealPowerAdmissibilityStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ) (B : BlockShape n) (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (B.Levi F.Carrier) V) (s : Fin B.length → ℝ),
      IsAdmissible (T.leviRealPowerTwist B s ρ) ↔ IsAdmissible ρ

/-- Arbitrary real determinant twists preserve irreducibility. -/
def LeviRealPowerIrreducibilityStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (n : ℕ) (B : BlockShape n) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (B.Levi F.Carrier) V) (s : Fin B.length → ℝ),
    Representation.IsIrreducible (T.leviRealPowerTwist B s ρ) ↔
      Representation.IsIrreducible ρ

/-- The actual fine twist of an irreducible cuspidal representation is
irreducible and admissible, and its flattened real twist remains cuspidal. -/
def FineTwistIrreducibleAdmissibleStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ) (B : BlockShape n) (S : BlockRefinement B)
      (ω : Rep.{uV} ℂ ((B.flatten S).Levi F.Carrier)),
      Representation.IsIrreducible ω.ρ →
      CuspidalSupport.IsLeviCuspidal (B.flatten S) ω.ρ →
      ∀ (v₀ : Fin (B.flatten S).length → ℝ) (t : Fin B.length → ℝ),
        let τ := RelativeJacquetMultiplicity.fineTwist T B S ω v₀ t
        Representation.IsIrreducible τ.ρ ∧ IsAdmissible τ.ρ ∧
          CuspidalSupport.IsLeviCuspidal (B.flatten S)
            (T.leviRealPowerTwist (B.flatten S)
              (fun k => -v₀ k + t ((B.flattenBlockEquiv S).symm k).1) ω.ρ)

/-- The full real-twist preservation interface and its actual fine specialization. -/
def FineTwistRegularityStatement : Prop :=
  LeviRealPowerCuspidalityStatement.{uF, uV} ∧
    LeviRealPowerAdmissibilityStatement.{uF, uV} ∧
    LeviRealPowerIrreducibilityStatement.{uF, uV} ∧
    FineTwistIrreducibleAdmissibleStatement.{uF, uV}

end Langlands

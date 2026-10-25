import Langlands.Representation.Parabolic.OppositeRefinementFunctors
import Langlands.Representation.Classification.CuspidalJacquetMultiplicityStatement
import Langlands.Representation.Geometric.FlattenedLevi

/-! Admissibility of the actual normalized opposite Jacquet representations. -/

namespace Langlands.Parabolic

open GeneralLinear Geometric

universe uF uV

/-- The standard opposite quotient, with its existing product-Levi action,
preserves admissibility. -/
def StandardOppositeJacquetAdmissibilityStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ) (B : BlockShape n)
      (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (GeneralLinear n F.Carrier) V),
      IsAdmissible ρ →
        IsAdmissible (CuspidalJacquetMultiplicity.oppositeJacquet T B (Rep.of ρ)).ρ

/-- The actual inner opposite quotient preserves admissibility for arbitrary
representations of the outer product Levi. -/
def RefinedOppositeJacquetAdmissibilityStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ) (B : BlockShape n) (S : BlockRefinement B)
      (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (B.Levi F.Carrier) V),
      IsAdmissible ρ →
        IsAdmissible (T.normalizedRefinedOppositeJacquet B S ρ)

/-- The actual full composed opposite quotient preserves admissibility. -/
def ComposedOppositeJacquetAdmissibilityStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ) (B : BlockShape n) (S : BlockRefinement B)
      (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (GeneralLinear n F.Carrier) V),
      IsAdmissible ρ →
        IsAdmissible (T.normalizedComposedOppositeJacquet B S ρ)

/-- The same refined quotient is admissible in the actual flattened
product-Levi coordinates. -/
def FlattenedRefinedOppositeJacquetAdmissibilityStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ) (B : BlockShape n) (S : BlockRefinement B)
      (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (B.Levi F.Carrier) V),
      IsAdmissible ρ →
        IsAdmissible ((T.normalizedRefinedOppositeJacquet B S ρ).comp
          (flattenedLeviEquiv F.Carrier B S).toMonoidHom)

/-- The same composed quotient is admissible in the actual flattened
product-Levi coordinates. -/
def FlattenedComposedOppositeJacquetAdmissibilityStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ) (B : BlockShape n) (S : BlockRefinement B)
      (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (GeneralLinear n F.Carrier) V),
      IsAdmissible ρ →
        IsAdmissible ((T.normalizedComposedOppositeJacquet B S ρ).comp
          (flattenedLeviEquiv F.Carrier B S).toMonoidHom)

/-- The complete opposite-admissibility interface, including the actual
flattened pullbacks used by the constituent comparison. -/
def NormalizedOppositeJacquetAdmissibilityStatement : Prop :=
  StandardOppositeJacquetAdmissibilityStatement.{uF, uV} ∧
  RefinedOppositeJacquetAdmissibilityStatement.{uF, uV} ∧
  ComposedOppositeJacquetAdmissibilityStatement.{uF, uV} ∧
  FlattenedRefinedOppositeJacquetAdmissibilityStatement.{uF, uV} ∧
  FlattenedComposedOppositeJacquetAdmissibilityStatement.{uF, uV}

end Langlands.Parabolic

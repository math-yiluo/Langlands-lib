import Langlands.Galois.CoefficientRepresentation
import Mathlib.LinearAlgebra.Trace
import Mathlib.RepresentationTheory.Semisimple

/-! # Finite coefficient fields for semisimple representations with rational trace -/

noncomputable section

universe uE uL uV

namespace Langlands.GaloisRepresentation

/-- A continuous semisimple representation over an algebraic closure, with
trace in the base coefficient field, has a matrix model over a finite extension.
The finite extension can contain any prescribed finite intermediate field. -/
def FiniteCoefficientModelStatement : Prop :=
  ∀ (E : Type uE) [Field E] (K C : Type uL) [Field K] [Field C] [CharZero C]
    [Algebra K C] [Algebra.IsAlgebraic K C] [IsAlgClosed C] [TopologicalSpace C]
    (A : Objects.{uE, uL, uV} E C) (Λ₀ : IntermediateField K C),
    FiniteDimensional K Λ₀ →
    Representation.IsSemisimpleRepresentation A.val.representation →
    (∀ g : Field.absoluteGaloisGroup E,
      LinearMap.trace C A.val (A.val.representation g) ∈ (algebraMap K C).range) →
    ∃ (b : Module.Basis (Fin A.val.rank) C A.val) (Λ : IntermediateField K C),
      Λ₀ ≤ Λ ∧ FiniteDimensional K Λ ∧
      ∀ (g : Field.absoluteGaloisGroup E) (i j : Fin A.val.rank),
        LinearMap.toMatrix b b (A.val.representation g) i j ∈ Λ

end Langlands.GaloisRepresentation

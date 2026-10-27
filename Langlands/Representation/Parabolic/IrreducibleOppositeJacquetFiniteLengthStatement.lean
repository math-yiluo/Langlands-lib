import Langlands.Representation.Classification.CuspidalJacquetMultiplicityStatement
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RingTheory.FiniteLength

/-!
# Finite length of opposite Jacquet modules of irreducible admissible input

Casselman (1995), Theorems 3.3.1 and 6.3.10, and Silberger (1979),
Theorem 5.4.1.6, specialized to the actual normalized opposite Jacquet
representation of an irreducible admissible representation of `GL_n(F)`.
This module defines the proposition and supplies no proof.
-/

namespace Langlands.Parabolic

universe uF uV

/-- The actual normalized opposite Jacquet representation of an irreducible
admissible complex representation of positive-rank `GL_n(F)` has finite
length over the complex group algebra of the actual product block Levi. -/
def IrreducibleOppositeJacquetFiniteLengthStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ (B : GeneralLinear.BlockShape n)
      (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (GeneralLinear n F.Carrier) V),
      Representation.IsIrreducible π → IsAdmissible π →
        IsFiniteLength (MonoidAlgebra ℂ (B.Levi F.Carrier))
          (CuspidalJacquetMultiplicity.oppositeJacquet T B (Rep.of π)).ρ.asModule

end Langlands.Parabolic

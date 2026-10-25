import Langlands.Representation.Classification.Cosocle
import Langlands.Representation.Filtration.MultiplicityStatement
import Langlands.Representation.Smooth.Schur.Proof

/-!
# Finite-length head multiplicity and intertwiner dimension

Internal algebraic statement targets. The source, target, and group universes
are independent, and composition-series existence is part of each conclusion.
-/

namespace Langlands.Classification

universe uG uV uW

/-- For a finite-length source and an admissible irreducible target, the
intertwiner space is finite-dimensional and its dimension is the target's
Jordan–Hölder multiplicity in the actual head of the source. -/
def HeadHomMultiplicityStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G]
    (A : Rep.{uV} ℂ G) (τ : Rep.{uW} ℂ G),
    IsFiniteLength (MonoidAlgebra ℂ G) A.ρ.asModule →
    IsAdmissible τ.ρ →
    Representation.IsIrreducible τ.ρ →
      FiniteDimensional ℂ (A.ρ.IntertwiningMap τ.ρ) ∧
      HasJordanHolderMultiplicity (Rep.of (head A.ρ)) τ
        (Module.finrank ℂ (A.ρ.IntertwiningMap τ.ρ))

/-- For a finite-length semisimple source, the multiplicity in the source itself
is the dimension of its intertwiner space to the admissible irreducible target. -/
def SemisimpleHomMultiplicityStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G]
    (A : Rep.{uV} ℂ G) (τ : Rep.{uW} ℂ G),
    IsFiniteLength (MonoidAlgebra ℂ G) A.ρ.asModule →
    Representation.IsSemisimpleRepresentation A.ρ →
    IsAdmissible τ.ρ →
    Representation.IsIrreducible τ.ρ →
      FiniteDimensional ℂ (A.ρ.IntertwiningMap τ.ρ) ∧
      HasJordanHolderMultiplicity A τ
        (Module.finrank ℂ (A.ρ.IntertwiningMap τ.ρ))

/-- The head and semisimple-source forms of the finite-length multiplicity/Hom
dimension bridge. This definition states both claims; it does not prove them. -/
def FiniteLengthHeadHomMultiplicityStatement : Prop :=
  HeadHomMultiplicityStatement.{uG, uV, uW} ∧
  SemisimpleHomMultiplicityStatement.{uG, uV, uW}

end Langlands.Classification

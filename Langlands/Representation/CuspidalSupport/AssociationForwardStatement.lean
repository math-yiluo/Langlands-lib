import Langlands.Representation.CuspidalSupport.NormalizedCuspidalInductionStatement
import Langlands.Representation.Induction.Parabolic

/-! Separate forward implications in BZ77 Theorem 2.9(a). -/

namespace Langlands.CuspidalSupport

open GeneralLinear

universe uF uV uW

/-- Associated irreducible cuspidal data give a nonzero actual intertwiner
between their canonical normalized inductions. -/
def AssociatedCuspidalInductionHomTheorem : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ), 0 < n →
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (B C : BlockShape n)
      (σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier))
      (τ : SmoothRep.{0, uF, uW} ℂ (C.Levi F.Carrier)),
      σ.IsIrreducible → IsLeviCuspidal B σ.representation →
      τ.IsIrreducible → IsLeviCuspidal C τ.representation →
      RepresentationsAssociated B C σ.representation τ.representation →
      ∃ f : (T.normalizedParabolicInduced B σ.representation).IntertwiningMap
          (T.normalizedParabolicInduced C τ.representation), f ≠ 0

/-- The two-block case of multiplicity-sensitive factor matching for
associated irreducible cuspidal inducing data. -/
def TwoBlockAssociatedCuspidalInductionFactorsTheorem : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ), 0 < n →
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (B C : BlockShape n)
      (σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier))
      (τ : SmoothRep.{0, uF, uW} ℂ (C.Levi F.Carrier)),
      B.length = 2 →
      σ.IsIrreducible → IsLeviCuspidal B σ.representation →
      τ.IsIrreducible → IsLeviCuspidal C τ.representation →
      RepresentationsAssociated B C σ.representation τ.representation →
      HaveSameJordanHolderFactors
        (Rep.of (T.normalizedParabolicInduced B σ.representation))
        (Rep.of (T.normalizedParabolicInduced C τ.representation))

/-- Associated irreducible cuspidal data have actual matching composition
series, with multiplicities and independent carrier universes. -/
def AssociatedCuspidalInductionFactorsTheorem : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ), 0 < n →
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (B C : BlockShape n)
      (σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier))
      (τ : SmoothRep.{0, uF, uW} ℂ (C.Levi F.Carrier)),
      σ.IsIrreducible → IsLeviCuspidal B σ.representation →
      τ.IsIrreducible → IsLeviCuspidal C τ.representation →
      RepresentationsAssociated B C σ.representation τ.representation →
      HaveSameJordanHolderFactors
        (Rep.of (T.normalizedParabolicInduced B σ.representation))
        (Rep.of (T.normalizedParabolicInduced C τ.representation))

/-- The separately accessible forward implications and their two-block
special case. These are proposition targets, not assumed theorem proofs. -/
def CuspidalAssociationForwardTheorems : Prop :=
  AssociatedCuspidalInductionHomTheorem.{uF, uV, uW} ∧
  TwoBlockAssociatedCuspidalInductionFactorsTheorem.{uF, uV, uW} ∧
  AssociatedCuspidalInductionFactorsTheorem.{uF, uV, uW}

end Langlands.CuspidalSupport

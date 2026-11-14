import Langlands.AllFieldBZ.Representation.CuspidalSupport.NormalizedCuspidalInductionStatement
import Langlands.AllFieldBZ.Representation.Induction.Parabolic
import Langlands.Representation.CuspidalSupport.AssociationForwardStatement

/-!
# All-field port of `Langlands.Representation.CuspidalSupport.AssociationForwardStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.CuspidalSupport.AssociationForwardStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.CuspidalSupport
open Langlands.CuspidalSupport hiding AssociatedCuspidalInductionFactorsTheorem AssociatedCuspidalInductionHomTheorem CuspidalEmbeddingTheorem CuspidalInductionLengthTheorem TwoBlockAssociatedCuspidalInductionFactorsTheorem
open Langlands.GeneralLinear
universe uF uV uW

/-- Associated irreducible cuspidal data give a nonzero actual intertwiner
between their canonical normalized inductions. -/
def AssociatedCuspidalInductionHomTheorem : Prop :=
  ∀ (F : LocalFieldPackage.{uF})
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
  ∀ (F : LocalFieldPackage.{uF})
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
  ∀ (F : LocalFieldPackage.{uF})
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

end Langlands.AllFieldBZ.CuspidalSupport

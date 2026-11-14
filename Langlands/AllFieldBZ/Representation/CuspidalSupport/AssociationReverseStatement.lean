import Langlands.AllFieldBZ.Representation.CuspidalSupport.NormalizedCuspidalInductionStatement
import Langlands.AllFieldBZ.Representation.Induction.Parabolic
import Langlands.Representation.CuspidalSupport.AssociationReverseStatement

/-!
# All-field port of `Langlands.Representation.CuspidalSupport.AssociationReverseStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.CuspidalSupport.AssociationReverseStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.CuspidalSupport
open Langlands.CuspidalSupport hiding CuspidalEmbeddingTheorem CuspidalInductionLengthTheorem CuspidalInductionReverseAssociationTheorem
open Langlands.GeneralLinear
universe uF uV uW

/-- A common actual irreducible subquotient of two canonical normalized
cuspidal inductions forces association of their inducing data. -/
def CuspidalInductionReverseAssociationTheorem
    (F : LocalFieldPackage.{uF})
    (T : F.TopologicalData) (n : ℕ) : Prop :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  ∀ (B C : BlockShape n)
    (σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier))
    (τ : SmoothRep.{0, uF, uW} ℂ (C.Levi F.Carrier)),
    σ.IsIrreducible → IsLeviCuspidal B σ.representation →
    τ.IsIrreducible → IsLeviCuspidal C τ.representation →
    HaveCommonIrreducibleSubquotient
      (SmoothRep.of (T.normalizedParabolicInduced B σ.representation)
        (T.isSmooth_normalizedParabolicInduced B σ.representation))
      (SmoothRep.of (T.normalizedParabolicInduced C τ.representation)
        (T.isSmooth_normalizedParabolicInduced C τ.representation)) →
    RepresentationsAssociated B C σ.representation τ.representation

end Langlands.AllFieldBZ.CuspidalSupport

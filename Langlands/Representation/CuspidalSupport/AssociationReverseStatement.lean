import Langlands.Representation.CuspidalSupport.NormalizedCuspidalInductionStatement
import Langlands.Representation.Induction.Parabolic
import Langlands.Representation.Filtration.CommonSubquotientStatement

/-! The common-subquotient-to-association direction of BZ77 Theorem 2.9(a). -/

namespace Langlands.CuspidalSupport

open GeneralLinear

universe uF uV uW

/-- A common actual irreducible subquotient of two canonical normalized
cuspidal inductions forces association of their inducing data. -/
def CuspidalInductionReverseAssociationTheorem
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
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

end Langlands.CuspidalSupport

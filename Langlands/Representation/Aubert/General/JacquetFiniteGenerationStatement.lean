import Langlands.Representation.Aubert.General.Parabolic
import Langlands.Representation.Induction.CompactQuotientProof

/-! The compact-quotient finite-generation input to general Jacquet finite length. -/

namespace Langlands.Aubert.General

universe uG uV

/-- Renard VI.1.3 for the actual normalized Jacquet functor, with compactness
of the actual parabolic left quotient retained as an explicit hypothesis. -/
def JacquetFiniteGenerationOfCompactQuotientStatement : Prop :=
  ∀ {G : Type uG} [Group G] [TopologicalSpace G]
    [LocallyCompactSpace G] [NonarchimedeanGroup G]
    {P M U : Subgroup G} (h : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G)) [CompactSpace (Induction.LeftQuotient P)]
    (A : SmoothRep.{0, uG, uV} ℂ G),
    Module.Finite (MonoidAlgebra ℂ G) A.representation.asModule →
      Module.Finite (MonoidAlgebra ℂ M)
        ((jacquetFunctor h hU).obj A).representation.asModule

end Langlands.Aubert.General

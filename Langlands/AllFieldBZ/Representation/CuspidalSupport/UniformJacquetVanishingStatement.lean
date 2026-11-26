import Langlands.AllFieldBZ.Representation.CuspidalSupport.JacquetInductionStatement
import Langlands.AllFieldBZ.Representation.CuspidalSupport.JacquetSubquotientStatement

/-! Divisibility of the target block sizes for nonzero Jacquet modules. -/

namespace Langlands.AllFieldBZ.CuspidalSupport

open Langlands.GeneralLinear Langlands.CuspidalSupport

universe uF uV

/-- For quasicuspidal induction from blocks of a common size, all target
block sizes of a nonzero Jacquet module of a subquotient are multiples of
that common size. -/
def UniformJacquetVanishingStatement (F : LocalFieldPackage.{uF}) (T : F.TopologicalData) : Prop :=
  letI := T.topology
  ∀ (n r : ℕ) (B C : BlockShape n), (∀ i, B.size i = r) →
    ∀ j : Fin C.length, ¬ r ∣ C.size j →
    ∀ A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier),
      IsLeviQuasicuspidal B A.representation →
      let I := (T.normalizedParabolicInductionFunctor B).obj A
      ∀ π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier),
        SmoothRep.IsSubquotient π I →
        Subsingleton ((T.normalizedJacquetFunctor C).obj π)

end Langlands.AllFieldBZ.CuspidalSupport

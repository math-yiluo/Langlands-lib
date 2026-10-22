import Langlands.Geometry.Analytic.TateUniversal.Definitions

/-! # Affinoid quotients defined by actual analytic relations -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedStrictAffinoidAlgebra

open StrictTateAlgebra

variable (K : Type u) [NormedField K] [IsUltrametricDist K]

/-- The actual affinoid algebra presented by Tate series relations.
Taking the topological closure constructs a closed ideal without assuming
that arbitrary ideals in the Tate algebra are closed. -/
def ofRelations (n : ℕ) (relations : Set (StrictTateAlgebra (Fin n) K)) :
    PresentedStrictAffinoidAlgebra K where
  arity := n
  ideal := (Ideal.span relations).closure
  ideal_closed := isClosed_closure

/-- A coordinate in the actual presented quotient. -/
def coordinate (A : PresentedStrictAffinoidAlgebra K) (i : Fin A.arity) : A :=
  presentationMap K A (X (Fin A.arity) K i)

theorem relation_mem (n : ℕ) (relations : Set (StrictTateAlgebra (Fin n) K))
    {f : StrictTateAlgebra (Fin n) K} (hf : f ∈ relations) :
    f ∈ (ofRelations K n relations).ideal :=
  subset_closure (Ideal.subset_span hf)

theorem presentationMap_relation (n : ℕ) (relations : Set (StrictTateAlgebra (Fin n) K))
    {f : StrictTateAlgebra (Fin n) K} (hf : f ∈ relations) :
    presentationMap K (ofRelations K n relations) f = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (relation_mem K n relations hf)

end Langlands.Analytic.PresentedStrictAffinoidAlgebra

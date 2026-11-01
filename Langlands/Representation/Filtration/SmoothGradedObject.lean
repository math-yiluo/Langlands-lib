import Langlands.Representation.Filtration.ObjectDefinitions
import Langlands.Representation.Category.Subquotients

/-! The shared actual smooth graded object of a finite representation filtration. -/

noncomputable section

universe uR uG uV

namespace Langlands.SmoothRep.IrreducibleGrothendieckProof

variable {k : Type uR} [Field k] {G : Type uG} [Group G] [TopologicalSpace G]
  {A : SmoothRep.{uR, uG, uV} k G} {n : ℕ}

/-- Bundle the existing actual graded representation with inherited smoothness. -/
def gradedSmooth (s : ObjectRepFiltration A.obj n) (i : Fin n) :
    SmoothRep.{uR, uG, uV} k G :=
  ⟨s.gradedRepresentation i,
    Langlands.isSmooth_of_surjective (s.gradedProjection i).hom
      (s.gradedProjection_surjective i)
      (subrepresentation A (s.subrepresentation i.succ)).isSmooth⟩

end Langlands.SmoothRep.IrreducibleGrothendieckProof

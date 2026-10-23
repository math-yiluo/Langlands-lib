import Langlands.AlgebraicGeometry.Modules.SectionLocus
import Langlands.AlgebraicGeometry.Picard.LineBundle

/-! # Openness target for the stalk-frame locus of a line-bundle section -/

universe u

open AlgebraicGeometry

namespace Langlands.SchemeModule

open Langlands.AlgebraicGeometry.Picard

/-- A line-bundle section has an open stalk-frame locus, equal to its full trivialization open. -/
def LineBundleStalkFrameOpen : Prop :=
  ∀ (X : Scheme.{u}) (L : LineBundle X) (s : GlobalSections L.obj),
    IsOpen {x : X | IsStalkFrame L.obj s x} ∧
      {x : X | IsStalkFrame L.obj s x} = (trivializationOpen L.obj s : Set X)

end Langlands.SchemeModule

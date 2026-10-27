import Langlands.AlgebraicGeometry.Modules.TensorSections
import Langlands.AlgebraicGeometry.Picard.LineBundle

/-! # The generation locus of a tensor product of line-bundle sections -/

universe u

open AlgebraicGeometry

namespace Langlands.SchemeModule

open Langlands.AlgebraicGeometry.Picard

/-- For two line bundles on an arbitrary scheme, the whole trivialization open of the
tensor product of two global sections is the intersection of their trivialization opens. -/
def TensorSectionGenerationLocusStatement : Prop :=
  ∀ (X : Scheme.{u}) (L M : LineBundle X)
    (s : GlobalSections L.obj) (t : GlobalSections M.obj),
    trivializationOpen (Langlands.Scheme.Modules.tensorObj L.obj M.obj)
        (tensorSection L.obj M.obj s t) =
      trivializationOpen L.obj s ⊓ trivializationOpen M.obj t

end Langlands.SchemeModule

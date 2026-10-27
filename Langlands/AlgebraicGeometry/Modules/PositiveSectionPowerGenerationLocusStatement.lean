import Langlands.AlgebraicGeometry.Modules.SectionLocus
import Langlands.AlgebraicGeometry.Modules.SectionPowers
import Langlands.AlgebraicGeometry.Picard.LineBundle

/-! # The generation locus of a positive power of a line-bundle section -/

universe u

namespace Langlands.SchemeModule

/-- For a line bundle on an arbitrary scheme and every positive exponent, the whole
trivialization open of the power of a global section is the whole trivialization open
of the section itself. -/
def PositiveSectionPowerGenerationLocusStatement : Prop :=
  ∀ (X : AlgebraicGeometry.Scheme.{u})
    (L : Langlands.AlgebraicGeometry.Picard.LineBundle X)
    (s : Langlands.SchemeModule.GlobalSections L.obj) (n : ℕ),
    0 < n →
    Langlands.SchemeModule.trivializationOpen
      (Langlands.Scheme.Modules.tensorPow L.obj n)
      (Langlands.SchemeModule.sectionPow L.obj s n) =
    Langlands.SchemeModule.trivializationOpen L.obj s

end Langlands.SchemeModule

import Langlands.AlgebraicGeometry.Modules.SectionPowers
import Langlands.AlgebraicGeometry.Picard.LineBundle
import Mathlib.Topology.QuasiSeparated

/-! # Clearing a scalar section on a line-bundle generation open -/

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Langlands.Scheme.Modules Langlands.AlgebraicGeometry.Picard

universe u

namespace Langlands.SchemeModule

/-- On a quasi-compact and quasi-separated scheme, every regular function on the
whole generation open of a line-bundle section becomes the restriction of a
global section of some nonnegative tensor power after multiplication by the
corresponding power section. -/
def LineBundleSectionClearingStatement : Prop :=
  ∀ (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (L : LineBundle X) (s : GlobalSections L.obj)
    (r : Γ(X, trivializationOpen L.obj s)),
    ∃ (m : ℕ) (a : GlobalSections (tensorPow L.obj m)),
      (tensorPow L.obj m).presheaf.map
        (homOfLE (show trivializationOpen L.obj s ≤ ⊤ from le_top)).op a =
        r • (tensorPow L.obj m).presheaf.map
          (homOfLE (show trivializationOpen L.obj s ≤ ⊤ from le_top)).op
          (sectionPow L.obj s m)

end Langlands.SchemeModule

import Langlands.AbelianScheme.PolarizedFiniteLevel.LargeLevelAmpleStatement
import Langlands.AbelianScheme.PolarizedFiniteLevel.LargeLevelQuasiProjectivityStatement
import Langlands.AlgebraicGeometry.Picard.AmpleHQuasiProjectiveStatement

/-! # Eventual quasi-projectivity from ample line bundles -/

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

set_option linter.defProp false in
/-- Proved definition: the general ample-immersion statement in universe zero and the
eventual existence of ample line bundles on representing level bases imply the published
target `LargeLevelQuasiProjectivityStatement`. -/
def largeLevelQuasiProjectivity_of_ample
    (Himm : Langlands.AlgebraicGeometry.Picard.AmpleHQuasiProjectiveStatement.{0})
    (Hample : LargeLevelAmpleStatement) :
    LargeLevelQuasiProjectivityStatement := by
  intro P g d hg hd
  obtain ⟨N, hN⟩ := Hample P g d hg hd
  refine ⟨N, fun n hNn hn X e => ?_⟩
  obtain ⟨hft, L, hL⟩ := hN n hNn hn X e
  have : CompactSpace X.obj := hL.compactSpace
  obtain ⟨m, i, hi, -, hcomp⟩ :=
    Himm (Localization.Away (n : ℤ)) X.obj X.toLocalizationSpec hft ⟨L, hL⟩
  exact ⟨inferInstance, m, i, hi, hcomp⟩

end Langlands.AbelianScheme.PolarizedFiniteLevel

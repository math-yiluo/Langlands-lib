import Langlands.Representation.Filtration.ExactSmoothTransport
import Langlands.Representation.Derivative.ShortExactFunctorLaws
import Langlands.Representation.Classification.SupercuspidalSupport

/-! Preservation of actual smooth subquotients by a supplied exact functor. -/

open CategoryTheory

namespace Langlands.ExactSmoothTransport

universe uG uH uV

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {H : Type uH} [Group H] [TopologicalSpace H]
  (J : SmoothRep.{0, uG, uV} ℂ G ⥤ SmoothRep.{0, uH, uV} ℂ H)
  (hJ : Derivative.Mirabolic.MapsShortExactIntertwiners J)

include hJ in
/-- Exactness preserves the existing actual subquotient relation. -/
theorem map_isSubquotient {A B : SmoothRep.{0, uG, uV} ℂ G}
    (h : SmoothRep.IsSubquotient B A) :
    SmoothRep.IsSubquotient (J.obj B) (J.obj A) := by
  obtain ⟨C, i, q, hi, hq⟩ := SmoothRep.isSubquotient_iff_exists.mp h
  exact SmoothRep.isSubquotient_iff_exists.mpr
    ⟨J.obj C, J.map i, J.map q, map_injective J hJ i hi,
      Derivative.LevelCalculus.map_surjective_of_exact hJ q hq⟩

end Langlands.ExactSmoothTransport

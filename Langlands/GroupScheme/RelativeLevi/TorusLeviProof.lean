import Langlands.GroupScheme.RelativeLevi.TorusDynamicCover
import Langlands.GroupScheme.RelativeLevi.TorusLeviPresentationReduction

/-! # The unique relative Levi containing a prescribed maximal torus -/

universe u

namespace Langlands.GroupScheme

/-- A maximal torus of a relative parabolic lies in a unique relative Levi,
over an arbitrary base scheme. -/
theorem relativeTorusLevi : RelativeTorusLeviStatement.{u} := by
  apply RelativeLevi.relativeTorusLevi_of_dynamicPresentation
  intro S G P i T t hG hi hT _ht hmax
  let d := RelativeLevi.torusDynamicPresentationCover i t hG hi hT hmax
  exact ⟨d.1, fun a => ⟨(d.2 a).cocharacter, (d.2 a).represents⟩⟩

end Langlands.GroupScheme

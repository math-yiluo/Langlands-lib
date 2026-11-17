import Langlands.GroupScheme.RelativeLevi.TorusDynamicPresentationStatement
import Langlands.GroupScheme.RelativeLevi.TorusDynamicCover

/-! # Étale local dynamic presentations along a prescribed maximal torus -/

universe u

namespace Langlands.GroupScheme

/-- Every relative parabolic has étale local dynamic presentations through
its prescribed fibrewise maximal relative torus. -/
theorem relativeTorusDynamicPresentation :
    RelativeTorusDynamicPresentationStatement.{u} := by
  intro S G P i T t hG hi hT _ht hmax
  obtain ⟨𝒰, h𝒰⟩ := RelativeLevi.torusDynamicPresentationCover i t hG hi hT hmax
  exact ⟨𝒰, fun a => ⟨(h𝒰 a).cocharacter, (h𝒰 a).represents⟩⟩

end Langlands.GroupScheme

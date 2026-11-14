import Langlands.GroupScheme.RelativeLevi.ParabolicLocalDynamicStatement
import Mathlib.AlgebraicGeometry.Cover.MorphismProperty

/-! # From an etale cover to pointwise dynamic presentations -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.RelativeLevi

/-- A dynamic presentation on an etale cover supplies the pointwise
neighbourhood premise used by the quotient and annihilation assemblies. -/
theorem pointwise_dynamic_of_etaleLocalDynamic
    (hlocal : Langlands.GroupScheme.RelativeParabolicEtaleLocalDynamicStatement.{u})
    {S : Scheme.{u}} {G P : GroupScheme S} (i : P ⟶ G)
    (hG : IsReductive G) (hP : IsRelativeParabolicSubgroup i) :
    ∀ s : S, ∃ (T : Scheme.{u}) (b : T ⟶ S), Etale b ∧
      (∃ t : T, b.base t = s) ∧
      ∃ χ : (Gm T).toGrp ⟶ (GroupScheme.baseChange b).obj G,
        (Dynamic.parabolic χ).IsRepresentedBy ((GroupScheme.baseChange b).map i) := by
  obtain ⟨𝒰, h𝒰⟩ := hlocal S G P i hG hP
  intro s
  have hcover := (Scheme.presieve₀_mem_precoverage_iff 𝒰.toPreZeroHypercover).mp 𝒰.mem₀
  obtain ⟨a, t, ht⟩ := hcover.1 s
  obtain ⟨χ, hχ⟩ := h𝒰 a
  exact ⟨𝒰.X a, 𝒰.f a, 𝒰.map_prop a, ⟨t, ht⟩, χ, hχ⟩

end Langlands.GroupScheme.RelativeLevi

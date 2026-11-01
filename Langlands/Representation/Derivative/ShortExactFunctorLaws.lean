import Langlands.Representation.Derivative.MirabolicMinusExactnessStatement

/-! Identity and composition laws for exact smooth-representation functors. -/

open CategoryTheory

namespace Langlands.Derivative.LevelCalculus

universe uV

variable {G : Type*} [Group G] [TopologicalSpace G] {H : Type*} [Group H] [TopologicalSpace H]
  {K : Type*} [Group K] [TopologicalSpace K]

open Mirabolic

theorem mapsShortExact_id :
    MapsShortExactIntertwiners (𝟭 (SmoothRep.{0, _, uV} ℂ G)) :=
  fun _ _ _ _ _ hi hq he => ⟨hi, he, hq⟩

theorem mapsShortExact_comp {J₁ : SmoothRep.{0, _, uV} ℂ G ⥤ SmoothRep.{0, _, uV} ℂ H}
    {J₂ : SmoothRep.{0, _, uV} ℂ H ⥤ SmoothRep.{0, _, uV} ℂ K}
    (h₁ : MapsShortExactIntertwiners J₁) (h₂ : MapsShortExactIntertwiners J₂) :
    MapsShortExactIntertwiners (J₁ ⋙ J₂) := fun A B C i q hi hq he =>
  let h := h₁ A B C i q hi hq he
  h₂ _ _ _ (J₁.map i) (J₁.map q) h.1 h.2.2 h.2.1

end Langlands.Derivative.LevelCalculus

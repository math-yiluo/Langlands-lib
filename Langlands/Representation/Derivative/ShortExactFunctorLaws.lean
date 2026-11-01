import Langlands.Representation.Derivative.MirabolicMinusExactnessStatement
import Langlands.Representation.Category.Subquotients

/-! Identity, composition and surjectivity laws for exact smooth-representation functors. -/

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

/-- Exactness preserves every actual surjective intertwiner, by its kernel sequence. -/
theorem map_surjective_of_exact
    {J : SmoothRep.{0, _, uV} ℂ G ⥤ SmoothRep.{0, _, uV} ℂ H}
    (hJ : MapsShortExactIntertwiners J) {B C : SmoothRep.{0, _, uV} ℂ G} (q : B ⟶ C)
    (hq : Function.Surjective (SmoothRep.hom q)) : Function.Surjective (SmoothRep.hom (J.map q)) := by
  apply (hJ (SmoothRep.kernel q) B C (SmoothRep.kernelι q) q
    (SmoothRep.subtype_injective _ _) hq ?_).2.2
  exact Submodule.range_subtype _

end Langlands.Derivative.LevelCalculus

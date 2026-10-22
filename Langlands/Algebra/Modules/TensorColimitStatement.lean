import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.CategoryTheory.Filtered.Basic

open CategoryTheory Limits MonoidalCategory

universe u

namespace Langlands.Algebra.Modules

/-- For a presheaf of commutative rings `R` on a small cofiltered category `C`, let `L` send a
presheaf of `R`-modules to the colimit over `Cᵒᵖ` of its underlying presheaf of abelian groups.
If `L` inverts `f : M₁ ⟶ M₂` and `g : N₁ ⟶ N₂`, then `L` inverts the sectionwise tensor
morphism `f ⊗ₘ g : M₁ ⊗ N₁ ⟶ M₂ ⊗ N₂`. This is a proposition, not an instance. -/
def tensorColimitIsIsoStatement (C : Type u) [SmallCategory C] [IsCofiltered C]
    (R : Cᵒᵖ ⥤ CommRingCat.{u}) : Prop :=
  let L : PresheafOfModulesOfCommRing.{u} R ⥤ AddCommGrpCat.{u} :=
    PresheafOfModules.toPresheaf.{u} (R ⋙ forget₂ CommRingCat RingCat) ⋙ colim
  ∀ (M₁ M₂ N₁ N₂ : PresheafOfModulesOfCommRing.{u} R) (f : M₁ ⟶ M₂) (g : N₁ ⟶ N₂),
    IsIso (L.map f) → IsIso (L.map g) → IsIso (L.map (f ⊗ₘ g))

end Langlands.Algebra.Modules

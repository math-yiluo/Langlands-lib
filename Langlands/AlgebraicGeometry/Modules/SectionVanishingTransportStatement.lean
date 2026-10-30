import Langlands.AlgebraicGeometry.Modules.SectionResidue

/-! # Zero tests and transport of actual pulled-back sections -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.SchemeModule

/-- Zero tests, composition, and naturality for the actual pullback of global sections. -/
def SectionVanishingTransportStatement : Prop :=
  (∀ (X : Scheme.{u}) (M : X.Modules) (s : GlobalSections M),
    sectionHom M s = 0 ↔ s = 0) ∧
  (∀ (X Y : Scheme.{u}) (f : Y ⟶ X) (M : X.Modules) (s : GlobalSections M),
    pullbackSection f M s = 0 ↔
      (Scheme.Modules.pullback f).map (sectionHom M s) = 0) ∧
  (∀ (X Y Z : Scheme.{u}) (f : Z ⟶ Y) (g : Y ⟶ X)
      (M : X.Modules) (s : GlobalSections M),
    pullbackSection f ((Scheme.Modules.pullback g).obj M) (pullbackSection g M s) = 0 ↔
      pullbackSection (f ≫ g) M s = 0) ∧
  (∀ (X Y : Scheme.{u}) (f : Y ⟶ X) [IsIso f]
      (M : X.Modules) (s : GlobalSections M),
    pullbackSection f M s = 0 ↔ s = 0) ∧
  (∀ (X Y : Scheme.{u}) (f : Y ⟶ X) (M N : X.Modules) (φ : M ⟶ N)
      (s : GlobalSections M),
    pullbackSection f N (φ.app ⊤ s) =
      ((Scheme.Modules.pullback f).map φ).app ⊤ (pullbackSection f M s)) ∧
  (∀ (X Y : Scheme.{u}) (f : Y ⟶ X) (M N : X.Modules) (e : M ≅ N)
      (s : GlobalSections M),
    pullbackSection f N (e.hom.app ⊤ s) = 0 ↔ pullbackSection f M s = 0)

end Langlands.SchemeModule

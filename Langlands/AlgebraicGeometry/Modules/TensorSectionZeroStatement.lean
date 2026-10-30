import Langlands.AlgebraicGeometry.Modules.TensorSections
import Langlands.AlgebraicGeometry.Modules.SectionResidue

/-! # Zero tests for tensor products of actual sections -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.SchemeModule

open Langlands.Scheme.Modules

/-- Zero factors, frame-factor cancellation, and pullback zero comparison for tensor sections. -/
def TensorSectionZeroStatement : Prop :=
  (∀ (X : Scheme.{u}) (M N : X.Modules) (t : GlobalSections N),
    tensorSection M N 0 t = 0) ∧
  (∀ (X : Scheme.{u}) (M N : X.Modules) (s : GlobalSections M),
    tensorSection M N s 0 = 0) ∧
  (∀ (X : Scheme.{u}) (M N : X.Modules)
      (s : GlobalSections M) (t : GlobalSections N) [IsIso (sectionHom N t)],
    tensorSection M N s t = 0 ↔ s = 0) ∧
  (∀ (X : Scheme.{u}) (M N : X.Modules)
      (s : GlobalSections M) (t : GlobalSections N) [IsIso (sectionHom M s)],
    tensorSection M N s t = 0 ↔ t = 0) ∧
  (∀ (X Y : Scheme.{u}) (f : Y ⟶ X) (M N : X.Modules)
      (s : GlobalSections M) (t : GlobalSections N),
    pullbackSection f (tensorObj M N) (tensorSection M N s t) = 0 ↔
      tensorSection ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N)
        (pullbackSection f M s) (pullbackSection f N t) = 0)

end Langlands.SchemeModule

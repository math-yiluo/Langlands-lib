import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.ObjectProperty.Small

/-! # Essential smallness of locally finitely presented module sheaves: statement -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules

/-- On every scheme in universe `u`, the locally finitely presented sheaves of
modules form an essentially `u`-small collection: there is a family indexed by a
type in `Type u` such that every locally finitely presented module sheaf is
isomorphic to a member of the family. -/
def FinitePresentationEssentiallySmallStatement : Prop :=
  ∀ Y : Scheme.{u},
    ObjectProperty.EssentiallySmall.{u}
      (SheafOfModules.isFinitePresentation.{u} Y.ringCatSheaf)

end Langlands.AlgebraicGeometry.Modules

import Mathlib.AlgebraicGeometry.Modules.Presheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
import Mathlib.CategoryTheory.Localization.Monoidal.Basic

open CategoryTheory

universe u

namespace Langlands.Scheme.Modules

/-- Local equivalences of module presheaves on an arbitrary scheme are stable under
sectionwise tensoring on either side. This is a proposition, not an instance. -/
def tensorLocalEquivalencesIsMonoidalStatement (X : AlgebraicGeometry.Scheme.{u}) : Prop :=
  let J := Opens.grothendieckTopology X
  let W : MorphismProperty (PresheafOfModulesOfCommRing.{u} X.presheaf) :=
    J.W.inverseImage (PresheafOfModules.toPresheaf.{u} X.ringCatSheaf.obj)
  W.IsMonoidal

end Langlands.Scheme.Modules

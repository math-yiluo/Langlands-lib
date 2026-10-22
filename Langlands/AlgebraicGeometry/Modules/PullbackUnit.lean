import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

open CategoryTheory

universe u

namespace Langlands.Scheme.Modules

open _root_.AlgebraicGeometry

variable {X Y Z : Scheme.{u}}

/-- The structure morphism of a scheme map, viewed as a morphism of module sheaves. -/
noncomputable def unitToPushforwardUnit (f : X ⟶ Y) :
    SheafOfModules.unit Y.ringCatSheaf ⟶
      (Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf) :=
  SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom

set_option backward.isDefEq.respectTransparency false in
/-- The canonical comparison from the pullback of the structure sheaf to the structure sheaf. -/
noncomputable def pullbackUnitIso (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).obj (SheafOfModules.unit Y.ringCatSheaf) ≅
      SheafOfModules.unit X.ringCatSheaf :=
  haveI : (TopologicalSpace.Opens.map f.base).Final := inferInstance
  haveI : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward f).IsRightAdjoint
  by
    let e := asIso (SheafOfModules.pullbackObjUnitToUnit
      (F := TopologicalSpace.Opens.map f.base) f.toRingCatSheafHom)
    exact e

end Langlands.Scheme.Modules

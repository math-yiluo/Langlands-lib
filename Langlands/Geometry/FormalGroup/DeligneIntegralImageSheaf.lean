import Langlands.Geometry.FormalGroup.DeligneExteriorSubsheaf
import Langlands.Geometry.FormalGroup.DeligneFrameDeterminant
import Langlands.Geometry.ModuleConstantSheaf

/-! # Actual component and integral-frame maps into rational Deligne sheaves -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.DeligneFormalSpace

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Langlands.ModuleSheaf

variable {O : Type u} [CommRing O] (F : Type u) [Field F] [Algebra O F]
  {X : TopCat.{u}} {d : ℕ} {π : O}

/-- The actual coordinatewise map from integral vectors to rational vectors. -/
def integralCoordinates (d : ℕ) :
    ModuleCat.of O (Fin d → O) ⟶
      (ModuleCat.restrictScalars (algebraMap O F)).obj
        (ModuleCat.of F (Fin d → F)) :=
  ModuleCat.homEquiv.symm (integralCoordinateRangeMap (O := O) F
    (V := ModuleCat.of F (Fin d → F)) LinearMap.id)

namespace LatticePiSheaf

variable (M : LatticePiSheaf d π X)

/-- The actual integral component inclusion followed by rationalization of the total sheaf. -/
def componentToRational (i : ZMod d) :
    M.component i ⟶ (rationalRestriction F X).obj (rationalLattice F X d π M.sheaf) :=
  M.inclusion i ≫ rationalUnit F X (latticeScalarSheaf d π X M.sheaf)

/-- This genuine sheaf map induces the previously constructed component stalk map. -/
theorem imageStalkMap_componentToRational (i : ZMod d) (x : X) :
    imageStalkMap (M.component i) (rationalLattice F X d π M.sheaf)
      (M.componentToRational F i) x = M.componentRationalStalkMap F i x := by
  let T := TopCat.Presheaf.stalkFunctor (ModuleCat.{u} O) x
  change T.map ((M.inclusion i).hom ≫
    (rationalUnit F X (latticeScalarSheaf d π X M.sheaf)).hom) ≫ _ = _
  rw [T.map_comp]
  rfl

end LatticePiSheaf

namespace FramedLatticePiSheaf

variable (M : FramedLatticePiSheaf d π X F)

/-- Integral constant vectors mapped into the genuine total rational presheaf by the frame. -/
def integralFramePresheafMap :
    (Functor.const (Opens X)ᵒᵖ).obj (ModuleCat.of O (Fin d → O)) ⟶
      ((rationalRestriction F X).obj (rationalLattice F X d π M.lattice.sheaf)).obj :=
  (Functor.const (Opens X)ᵒᵖ).map (integralCoordinates F d) ≫
    Functor.whiskerRight
      (toSheafify (Opens.grothendieckTopology X)
        ((Functor.const (Opens X)ᵒᵖ).obj (ModuleCat.of F (Fin d → F))) ≫
          (M.frameToTotal F).hom)
      (ModuleCat.restrictScalars (algebraMap O F))

/-- The actual map from the constant integral vector sheaf induced by the rational frame. -/
def integralFrameSheafMap :
    (constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} O)).obj
      (ModuleCat.of O (Fin d → O)) ⟶
        (rationalRestriction F X).obj (rationalLattice F X d π M.lattice.sheaf) where
  hom := sheafifyLift (Opens.grothendieckTopology X) (M.integralFramePresheafMap F)
    ((rationalRestriction F X).obj (rationalLattice F X d π M.lattice.sheaf)).property

/-- The constructed sheaf map has the specified value on every constant section. -/
theorem integralFrameSheafMap_unit (U : (Opens X)ᵒᵖ) :
    (toSheafify (Opens.grothendieckTopology X)
      ((Functor.const (Opens X)ᵒᵖ).obj (ModuleCat.of O (Fin d → O)))).app U ≫
        (M.integralFrameSheafMap F).hom.app U =
      (M.integralFramePresheafMap F).app U :=
  congrArg (fun k => k.app U) (toSheafify_sheafifyLift
    (Opens.grothendieckTopology X) (M.integralFramePresheafMap F)
    ((rationalRestriction F X).obj (rationalLattice F X d π M.lattice.sheaf)).property)

/-- Constant integral vector germs recover the previously constructed integral frame map. -/
theorem integralFrameSheafMap_germ (x : X) :
    (toSheafify (Opens.grothendieckTopology X)
      ((Functor.const (Opens X)ᵒᵖ).obj (ModuleCat.of O (Fin d → O)))).app (.op ⊤) ≫
        (M.integralFrameSheafMap F).hom.app (.op ⊤) ≫
          TopCat.Presheaf.Γgerm
            ((rationalRestriction F X).obj (rationalLattice F X d π M.lattice.sheaf)).obj x ≫
              (restrictionStalkIso F X (rationalLattice F X d π M.lattice.sheaf) x).hom =
      ModuleCat.ofHom (M.integralFrameStalkMap F x) := by
  rw [← Category.assoc, ← Category.assoc, M.integralFrameSheafMap_unit]
  have hg := restrictionStalkIso_germ (O := O)
    (rationalLattice F X d π M.lattice.sheaf) (⊤ : Opens X) x (Set.mem_univ x)
  change TopCat.Presheaf.Γgerm
      ((rationalRestriction F X).obj (rationalLattice F X d π M.lattice.sheaf)).obj x ≫
        (restrictionStalkIso F X (rationalLattice F X d π M.lattice.sheaf) x).hom =
      (ModuleCat.restrictScalars (algebraMap O F)).map
        (TopCat.Presheaf.Γgerm (rationalLattice F X d π M.lattice.sheaf).obj x) at hg
  rw [Category.assoc, hg]
  ext v
  rfl

/-- The actual stalk image of the integral-frame sheaf map is exactly r O^d. -/
theorem imageStalkMap_integralFrameSheafMap_range (x : X) :
    LinearMap.range (imageStalkMap
      ((constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} O)).obj
        (ModuleCat.of O (Fin d → O)))
      (rationalLattice F X d π M.lattice.sheaf) (M.integralFrameSheafMap F) x).hom =
      M.frameStalkLattice F x := by
  change LinearMap.range
    ((restrictionStalkIso F X (rationalLattice F X d π M.lattice.sheaf) x).hom.hom.comp
      ((TopCat.Presheaf.stalkFunctor (ModuleCat.{u} O) x).map
        (M.integralFrameSheafMap F).hom).hom) = _
  rw [LinearMap.range_comp, constantSheaf_stalk_range]
  rw [← LinearMap.range_comp]
  exact congrArg (fun k => LinearMap.range k.hom) (M.integralFrameSheafMap_germ F x)

end FramedLatticePiSheaf

end Langlands.DeligneFormalSpace

import Langlands.Geometry.FormalGroup.DeligneSheafPreDatum
import Mathlib.CategoryTheory.Linear.FunctorCategory
import Mathlib.Algebra.Group.Commute.Units

/-! # Rationalization and the invertible rational Deligne operator -/

noncomputable section

universe u

namespace Langlands.DeligneFormalSpace

open CategoryTheory TopologicalSpace
open scoped ChangeOfRings

variable {O : Type u} [CommRing O] (F : Type u) [Field F] [Algebra O F]
  (X : TopCat.{u})

/-- Scalar extension of an actual O-sheaf, before sheafification. -/
def rationalPresheafFunctor :
    X.Sheaf (ModuleCat.{u} O) ⥤ (Opens X)ᵒᵖ ⥤ ModuleCat.{u} F :=
  sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{u} O) ⋙
    (Functor.whiskeringRight _ _ _).obj (ModuleCat.extendScalars (algebraMap O F))

/-- Rationalization is scalar extension on sections followed by actual sheafification. -/
def rationalSheafFunctor : X.Sheaf (ModuleCat.{u} O) ⥤ X.Sheaf (ModuleCat.{u} F) :=
  rationalPresheafFunctor F X ⋙
    presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} F)

/-- Forget the rational scalar field while retaining the actual sheaf. -/
def rationalRestriction : X.Sheaf (ModuleCat.{u} F) ⥤ X.Sheaf (ModuleCat.{u} O) :=
  sheafCompose (Opens.grothendieckTopology X) (ModuleCat.restrictScalars (algebraMap O F))

/-- The integral map m ↦ 1 ⊗ m, followed by the sheafification map. -/
def rationalUnit (M : X.Sheaf (ModuleCat.{u} O)) :
    M ⟶ (rationalRestriction F X).obj ((rationalSheafFunctor F X).obj M) where
  hom :=
    Functor.whiskerLeft M.obj (ModuleCat.extendRestrictScalarsAdj (algebraMap O F)).unit ≫
      Functor.whiskerRight
        (toSheafify (Opens.grothendieckTopology X)
          ((rationalPresheafFunctor F X).obj M))
        (ModuleCat.restrictScalars (algebraMap O F))

set_option backward.isDefEq.respectTransparency false in
/-- The integral map commutes with every actual O-sheaf morphism. -/
theorem rationalUnit_naturality {M N : X.Sheaf (ModuleCat.{u} O)} (f : M ⟶ N) :
    f ≫ rationalUnit F X N =
      rationalUnit F X M ≫
        (rationalRestriction F X).map ((rationalSheafFunctor F X).map f) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  let R := ModuleCat.restrictScalars (algebraMap O F)
  let E := rationalPresheafFunctor (O := O) F X
  let j := Opens.grothendieckTopology X
  let v := (ModuleCat.extendRestrictScalarsAdj (algebraMap O F)).unit
  change f.hom.app U ≫ (v.app (N.obj.obj U) ≫
    R.map ((toSheafify j (E.obj N)).app U)) =
    (v.app (M.obj.obj U) ≫ R.map ((toSheafify j (E.obj M)).app U)) ≫
      R.map ((sheafifyMap j (E.map f)).app U)
  have h : f.hom.app U ≫ v.app (N.obj.obj U) =
      v.app (M.obj.obj U) ≫ R.map ((E.map f).app U) :=
    v.naturality (f.hom.app U)
  rw [← Category.assoc, h, Category.assoc, Category.assoc,
    ← R.map_comp, ← R.map_comp]
  exact congrArg (fun k => v.app (M.obj.obj U) ≫ R.map k)
    (congrArg (fun k => k.app U) (toSheafify_naturality j (E.map f)))

variable (d : ℕ) (π : O)

/-- The total rational lattice sheaf, without selecting a homogeneous component. -/
def rationalLattice (M : X.Sheaf (ModuleCat.{u} (PiAlgebra d π))) :
    X.Sheaf (ModuleCat.{u} F) :=
  (rationalSheafFunctor F X).obj (latticeScalarSheaf d π X M)

/-- The actual total Pi operator after extension of scalars, before sheafification. -/
def rationalPiPresheaf (M : X.Sheaf (ModuleCat.{u} (PiAlgebra d π))) :
    End ((rationalPresheafFunctor F X).obj (latticeScalarSheaf d π X M)) :=
  (rationalPresheafFunctor F X).map (latticePi d π X M)

set_option backward.isDefEq.respectTransparency false in
/-- On pure tensors, every positive iterate is the corresponding integral Pi power. -/
theorem rationalPiPresheaf_pow_tmul
    (M : X.Sheaf (ModuleCat.{u} (PiAlgebra d π))) (U : (Opens X)ᵒᵖ)
    (n : ℕ) (a : F) (m : (latticeScalarSheaf d π X M).obj.obj U) :
    ((rationalPiPresheaf F X d π M ^ n).app U)
      (a ⊗ₜ[O, algebraMap O F] m) =
        a ⊗ₜ[O, algebraMap O F] ((((latticePi d π X M).hom.app U).hom ^ n) m) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    change (ModuleCat.extendScalars (algebraMap O F)).map
      ((latticePi d π X M).hom.app U)
        (((rationalPiPresheaf F X d π M ^ n).app U)
          (a ⊗ₜ[O, algebraMap O F] m)) = _
    rw [ih, ModuleCat.ExtendScalars.map_tmul, pow_succ']
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- The rational total operator has d-th power equal to the actual scalar pi. -/
theorem rationalPiPresheaf_relation
    (M : X.Sheaf (ModuleCat.{u} (PiAlgebra d π))) :
    rationalPiPresheaf F X d π M ^ d =
      algebraMap F (End ((rationalPresheafFunctor F X).obj
        (latticeScalarSheaf d π X M))) (algebraMap O F π) := by
  apply NatTrans.ext
  funext U
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  refine (rationalPiPresheaf_pow_tmul F X d π M U d 1 m).trans ?_
  rw [show ((((latticePi d π X M).hom.app U).hom ^ d) m) = π • m from
    latticePi_relation d π X M U m]
  change (1 : F) ⊗ₜ[O, algebraMap O F]
      (π • (m : (latticeScalarSheaf d π X M).obj.obj U)) =
    algebraMap O F π • ((1 : F) ⊗ₜ[O, algebraMap O F] m)
  exact ((ModuleCat.extendRestrictScalarsAdj (algebraMap O F)).unit.app
    ((latticeScalarSheaf d π X M).obj.obj U)).hom.map_smul π m

variable [NeZero d]

/-- Nonvanishing of pi in F makes the actual total rational operator a unit. -/
theorem rationalPiPresheaf_isUnit
    (M : X.Sheaf (ModuleCat.{u} (PiAlgebra d π))) (hπ : algebraMap O F π ≠ 0) :
    IsUnit (rationalPiPresheaf F X d π M) := by
  apply (isUnit_pow_iff (NeZero.ne d)).mp
  rw [rationalPiPresheaf_relation]
  exact (isUnit_iff_ne_zero.mpr hπ).map (algebraMap F _)

/-- The actual invertible total rational Pi operator, as an automorphism of sheaves. -/
def rationalPiAut (M : X.Sheaf (ModuleCat.{u} (PiAlgebra d π)))
    (hπ : algebraMap O F π ≠ 0) : Aut (rationalLattice F X d π M) :=
  (presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} F)).mapIso
    ((Aut.unitsEndEquivAut _)
      (rationalPiPresheaf_isUnit F X d π M hπ).unit)

/-- The automorphism's forward map is the rationalization of the integral operator. -/
theorem rationalPiAut_hom (M : X.Sheaf (ModuleCat.{u} (PiAlgebra d π)))
    (hπ : algebraMap O F π ≠ 0) :
    (rationalPiAut F X d π M hπ).hom =
      (rationalSheafFunctor F X).map (latticePi d π X M) := by
  change (presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} F)).map
    (rationalPiPresheaf_isUnit F X d π M hπ).unit.val = _
  rw [IsUnit.unit_spec]
  rfl

end Langlands.DeligneFormalSpace

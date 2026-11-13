import Langlands.Geometry.FormalGroup.DeligneLineSheaf
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.ConcreteSheafification
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.RingTheory.Flat.Basic

/-! # The actual flat lattice sheaf and its rational frame in Deligne's data -/

noncomputable section

universe u

namespace Langlands.DeligneFormalSpace

open CategoryTheory TopologicalSpace

variable (d : ℕ) {O : Type u} [CommRing O] (π : O) (X : TopCat.{u})

/-- Restrict an actual O[Pi]-module sheaf to its O-module sheaf. -/
def latticeScalarSheaf (M : X.Sheaf (ModuleCat.{u} (PiAlgebra d π))) :
    X.Sheaf (ModuleCat.{u} O) :=
  (sheafCompose (Opens.grothendieckTopology X)
    (ModuleCat.restrictScalars (algebraMap O (PiAlgebra d π)))).obj M

/-- Multiplication by the actual distinguished generator as a coefficient-linear sheaf map. -/
def latticePiIntegral (M : X.Sheaf (ModuleCat.{u} (PiAlgebra d π))) : M ⟶ M where
  hom := {
    app U := ModuleCat.ofHom (LinearMap.lsmul (PiAlgebra d π) (M.obj.obj U) (PiAlgebra.pi d π))
    naturality {U V} f := by
      ext x
      exact ((M.obj.map f).hom.map_smul (PiAlgebra.pi d π) x).symm }

/-- The same multiplication, after restriction of scalars to O. -/
def latticePi (M : X.Sheaf (ModuleCat.{u} (PiAlgebra d π))) :
    latticeScalarSheaf d π X M ⟶ latticeScalarSheaf d π X M :=
  (sheafCompose (Opens.grothendieckTopology X)
    (ModuleCat.restrictScalars (algebraMap O (PiAlgebra d π)))).map
      (latticePiIntegral d π X M)

set_option backward.isDefEq.respectTransparency false in
/-- Iteration of the constructed operator is scalar multiplication by the corresponding power. -/
theorem latticePi_pow_apply (M : X.Sheaf (ModuleCat.{u} (PiAlgebra d π)))
    (U : (Opens X)ᵒᵖ) (n : ℕ) (x : M.obj.obj U) :
    (((latticePi d π X M).hom.app U).hom ^ n) x = PiAlgebra.pi d π ^ n • x := by
  let P : Module.End O ((latticeScalarSheaf d π X M).obj.obj U) :=
    ((latticePi d π X M).hom.app U).hom
  change (P ^ n) x = PiAlgebra.pi d π ^ n • x
  induction n with
  | zero =>
    change x = (1 : PiAlgebra d π) • x
    exact (one_smul _ x).symm
  | succ n ih =>
    rw [pow_succ']
    change P ((P ^ n) x) = PiAlgebra.pi d π ^ (n + 1) • x
    rw [ih, pow_succ', mul_smul]
    rfl

/-- The actual relation holds on the O-module sheaf, without an extra operator axiom. -/
theorem latticePi_relation (M : X.Sheaf (ModuleCat.{u} (PiAlgebra d π)))
    (U : (Opens X)ᵒᵖ) (x : M.obj.obj U) :
    (((latticePi d π X M).hom.app U).hom ^ d) x =
      algebraMap O (PiAlgebra d π) π • x := by
  rw [latticePi_pow_apply, PiAlgebra.pi_pow]

variable [NeZero d]

/-- The flat graded O[Pi]-sheaf eta, with an actual decomposition after restriction to O. -/
structure LatticePiSheaf where
  sheaf : X.Sheaf (ModuleCat.{u} (PiAlgebra d π))
  flat (x : X) : Module.Flat (PiAlgebra d π) (TopCat.Presheaf.stalk (C := ModuleCat.{u} (PiAlgebra d π)) (X := X) sheaf.obj x)
  component : ZMod d → X.Sheaf (ModuleCat.{u} O)
  inclusion (i : ZMod d) : component i ⟶ latticeScalarSheaf d π X sheaf
  injective (i : ZMod d) (U : (Opens X)ᵒᵖ) :
    Function.Injective ((inclusion i).hom.app U)
  isInternal (U : (Opens X)ᵒᵖ) :
    DirectSum.IsInternal (fun i => LinearMap.range ((inclusion i).hom.app U).hom)
  pi (i : ZMod d) : component i ⟶ component (i + 1)
  pi_inclusion (i : ZMod d) :
    pi i ≫ inclusion (i + 1) = inclusion i ≫ latticePi d π X sheaf

namespace LatticePiSheaf

variable {d π X} (M : LatticePiSheaf d π X)

/-- The actual homogeneous inclusion is a sheaf monomorphism. -/
instance inclusion_mono (i : ZMod d) : Mono (M.inclusion i) := by
  let : ∀ U, Mono (((sheafToPresheaf (Opens.grothendieckTopology X)
      (ModuleCat.{u} O)).map (M.inclusion i)).app U) :=
    fun U => (ModuleCat.mono_iff_injective _).mpr (M.injective i U)
  exact (sheafToPresheaf _ _).mono_of_mono_map (NatTrans.mono_of_mono_app _)

/-- Rationalization is actual scalar extension on sections followed by sheafification. -/
def rationalComponent (F : Type u) [Field F] [Algebra O F] (i : ZMod d) :
    X.Sheaf (ModuleCat.{u} F) :=
  (presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} F)).obj
    ((M.component i).obj ⋙ ModuleCat.extendScalars (algebraMap O F))

end LatticePiSheaf

variable (F : Type u) [Field F] [Algebra O F]

/-- The full rational frame is a K-linear isomorphism from the actual constant rank-d sheaf. -/
structure FramedLatticePiSheaf where
  lattice : LatticePiSheaf d π X
  frame : (constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} F)).obj
    (ModuleCat.of F (Fin d → F)) ≅ lattice.rationalComponent F 0

end Langlands.DeligneFormalSpace

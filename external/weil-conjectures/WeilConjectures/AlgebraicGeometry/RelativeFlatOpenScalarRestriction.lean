/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
import WeilConjectures.AlgebraicGeometry.RelativeFlatModuleStalk
import WeilConjectures.AlgebraicGeometry.OpenScalarRestrictionStalkCriterion
import WeilConjectures.AlgebraicGeometry.InverseImageStructureStalkIso
import Mathlib.RingTheory.RingHom.Flat

/-! # Relative flatness on an open localized site

Source: Stacks Project, Tags 01U2, 05NE and 0098.
(blueprint: lem-pc-relative-flat-open-scalar-restriction).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory TopologicalSpace
namespace AlgebraicGeometry.Scheme

/-- Restricting an affine-locally base-flat module to an open site and restricting
scalars along the inverse-image structure map yields a flat module over that ring.
Source: Stacks Project, Tags 01U2, 05NE and 0098.
(blueprint: lem-pc-relative-flat-open-scalar-restriction).

Proof: for every point x of U, use relative_flat_module_stalk to obtain flatness of
G_x over O_S,f(x). The stalk of the inverse-image ring is canonically O_S,f(x),
and the scalar-restricted module stalk is G_x with its action induced by f.stalkMap x.
Restriction to the localized open site preserves these stalks. Under the canonical
ring and module isomorphisms its stalks are therefore flat. For an exact short complex
of modules over the inverse-image ring on U, tensor and stalk commute, so tensoring
with this module preserves exactness on every stalk. Stalks detect exactness; the
additive tensor functor consequently preserves finite limits and colimits, giving
IsFlat. No quasi-coherence is needed. If U is empty the stalk test is vacuous; the
zero module is covered by the same argument. -/
theorem relativeFlat_open_scalarRestriction
    {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens) (G : X.Modules)
    (hflat : G.IsFlatOver f) :
    let α := ((Opens.grothendieckTopology X).overPullback CommRingCat.{u} U).map
      (Modules.tensorPullbackRingMap f)
    let B := (sheafCompose ((Opens.grothendieckTopology X).over U)
      (forget₂ CommRingCat.{u} RingCat.{u})).map α
    SheafOfModules.IsFlat ((SheafOfModules.restrictScalars B).obj
      ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).obj G)) := by
  apply RingedSpace.isFlat_open_scalarRestriction_of_stalks X.toRingedSpace
    (TopCat.Sheaf.inverseImageRing f.base S.sheaf) (Modules.tensorPullbackRingMap f)
  intro x hx
  let A := S.presheaf.stalk (f x)
  let B := (TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).obj
    (TopCat.Sheaf.inverseImageRing f.base S.sheaf).obj
  let C := X.presheaf.stalk x
  let ψ : B ⟶ C := (TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
    (Modules.tensorPullbackRingMap f).hom
  let M := (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj G
  obtain ⟨e, he⟩ := exists_inverseImageStructure_stalk_iso f x
  let : Algebra A C := (f.stalkMap x).hom.toAlgebra
  have hM := relative_flat_module_stalk f G hflat x rfl
  let N := (ModuleCat.restrictScalars ψ.hom).obj M
  let : Algebra B A := e.inv.hom.toAlgebra
  let : Module A N := Module.compHom M (f.stalkMap x).hom
  have : IsScalarTower B A N := by
    constructor
    intro b a m
    change (f.stalkMap x).hom (e.inv.hom b * a) • m =
      ψ.hom b • ((f.stalkMap x).hom a • m)
    rw [map_mul, mul_smul]
    congr 1
    have hc : e.inv ≫ f.stalkMap x = ψ := by
      rw [← he]
      simp only [Iso.inv_hom_id_assoc]
      rfl
    exact ConcreteCategory.congr_hom hc b
  have : Module.Flat A N := hM
  have : Module.Flat B A := RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso e.inv)
  exact Module.Flat.trans B A N

end AlgebraicGeometry.Scheme

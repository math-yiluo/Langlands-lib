/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import Mathlib.Topology.Sheaves.Flasque
public import Mathlib.AlgebraicGeometry.Scheme
import WeilConjectures.AlgebraicGeometry.ModuleAbelianZariskiCohomology
import WeilConjectures.Topology.FlasqueZariskiAcyclic
import WeilConjectures.AlgebraicGeometry.ZariskiModuleAbelianCohomologyNatural

/-! # Flasque module sheaves are acyclic for module global sections

Source: Stacks Project, Tag 01E1 (flasque modules) and Tag 03FD (comparison).
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry

/-- Flasqueness of a module's underlying abelian sheaf implies module cohomology vanishes.
Source: Stacks Project, Tags 01E1 and 03FD.
(blueprint: lem-sc-module-cup-flasque-acyclicity)
Proof: compare the underlying abelian group of module cohomology with the cohomology
of the underlying abelian sheaf. Flasque acyclicity makes the latter group zero in
positive degrees, hence the former is zero. The forgetful functor reflects zero objects.
Together with the acyclic-resolution comparison theorem, this makes any nonnegative
exact augmented resolution with flasque terms a computing resolution. -/
theorem moduleCup_flasque_acyclicity (X : Scheme.{u})
    (F : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    [TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf
      (moduleRings X.toRingedSpace)).obj F)] (q : ℕ) (hq : 0 < q) :
    IsZero ((RingedSpace.moduleCohomology X.toRingedSpace q).obj F) := by
  let : EnoughInjectives (Sheaf (Opens.grothendieckTopology X.carrier)
      AddCommGrpCat.{u}) :=
    @IsGrothendieckAbelian.enoughInjectives _ _ _
      (Sheaf.isGrothendieckAbelian_of_essentiallySmall'.{u}
        (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})
  let : HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) :=
    hasExt_of_enoughInjectives _
  obtain ⟨e⟩ := module_cohomology_iso_underlying_abelian X F q
  have : Subsingleton (Sheaf.H' ((SheafOfModules.toSheaf
      (moduleRings X.toRingedSpace)).obj F) q ⊤) :=
    TopCat.Sheaf.IsFlasque.subsingleton_H'_top _ q hq
  apply ModuleCat.isZero_iff_subsingleton.mpr
  exact e.addCommGroupIsoToAddEquiv.injective.subsingleton

end AlgebraicGeometry

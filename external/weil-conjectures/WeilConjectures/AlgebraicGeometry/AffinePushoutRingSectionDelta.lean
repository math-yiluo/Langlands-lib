/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Topology.InverseImageModule
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped ChangeOfRings TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
variable {U X : Scheme.{u}} (f : U ⟶ X)
set_option hygiene false in
local notation "A" => (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj U.sheaf
set_option hygiene false in
local notation "ρ" => (show X.sheaf ⟶ A from ⟨f.c⟩)
set_option hygiene false in
local notation "IA" => TopCat.Sheaf.inverseImageRing f.base A
set_option hygiene false in
local notation "r₀" => tensorPullbackRingMap f
set_option hygiene false in
local notation "t₀" =>
  (TopCat.Sheaf.inverseImageConstruction f.base CommRingCat.{u}).map ρ

local instance instHasLeftKanExtension_affinePushoutRingSectionDelta
    (F : (Opens X)ᵒᵖ ⥤ CommRingCat.{u}) :
    (Opens.map f.base).op.HasLeftKanExtension F :=
  Functor.HasLeftKanExtension.mk _
    (Functor.pointwiseLeftKanExtensionUnit (Opens.map f.base).op F)

/-- The second section-ring leg is the inverse-image unit followed by `t`.
Source: Stacks Project, Tag 01SB (blueprint: stage3-affine-pushout-ring-section-delta). -/
def affinePushoutSectionDelta (B : U.toTopCat.Sheaf CommRingCat.{u}) (t : IA ⟶ B)
    (V : X.Opens) : Γ(U, f ⁻¹ᵁ V) →+* B.obj.obj (op (f ⁻¹ᵁ V)) :=
  (t.hom.app (op (f ⁻¹ᵁ V))).hom.comp
    (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (Opens.map f.base) CommRingCat.{u} (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology U)).unit.app A).hom.app (op V)).hom

end
end AlgebraicGeometry.Scheme.Modules

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.AffinePushoutRingSectionDelta
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
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
/-- The section legs agree on the base ring, by the adjunction unit and pushout equation.
Source: Stacks Project, Tag 01SB (blueprint: stage3-affine-pushout-ring-section-comm). -/
theorem affinePushoutSection_comm
    (B : U.toTopCat.Sheaf CommRingCat.{u}) (b : U.sheaf ⟶ B) (t : IA ⟶ B)
    (hpushout : IsPushout r₀ t₀ b t) (V : X.Opens) :
    f.app V ≫ b.hom.app (op (f ⁻¹ᵁ V)) =
      f.app V ≫ CommRingCat.ofHom (affinePushoutSectionDelta f B t V) := by
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Opens.map f.base) CommRingCat.{u} (Opens.grothendieckTopology X)
    (Opens.grothendieckTopology U)
  have hr := adj.homEquiv X.sheaf U.sheaf |>.apply_symm_apply
    (show X.sheaf ⟶ _ from ⟨f.c⟩)
  rw [Adjunction.homEquiv_unit] at hr
  have hn := adj.unit_naturality ρ
  have hp := hpushout.w
  ext x
  have hrx := congrArg (fun q ↦ q.hom.app (op V) x) hr
  have hnx := congrArg (fun q ↦ q.hom.app (op V) x) hn
  have hpx := congrArg (fun q ↦ q.hom.app (op (f ⁻¹ᵁ V))
    ((adj.unit.app X.sheaf).hom.app (op V) x)) hp
  change (b.hom.app (op (f ⁻¹ᵁ V))).hom ((f.app V).hom x) =
    (t.hom.app (op (f ⁻¹ᵁ V))).hom
      ((adj.unit.app A).hom.app (op V) ((f.app V).hom x))
  change (tensorPullbackRingMap f).hom.app (op (f ⁻¹ᵁ V))
    ((adj.unit.app X.sheaf).hom.app (op V) x) = (f.app V).hom x at hrx
  change (t₀).hom.app (op (f ⁻¹ᵁ V))
    ((adj.unit.app X.sheaf).hom.app (op V) x) =
    (adj.unit.app A).hom.app (op V) ((f.app V).hom x) at hnx
  change (b.hom.app (op (f ⁻¹ᵁ V))).hom
    ((tensorPullbackRingMap f).hom.app (op (f ⁻¹ᵁ V))
      ((adj.unit.app X.sheaf).hom.app (op V) x)) =
    (t.hom.app (op (f ⁻¹ᵁ V))).hom
      ((t₀).hom.app (op (f ⁻¹ᵁ V)) ((adj.unit.app X.sheaf).hom.app (op V) x)) at hpx
  simpa only [hrx, hnx] using hpx

end
end AlgebraicGeometry.Scheme.Modules

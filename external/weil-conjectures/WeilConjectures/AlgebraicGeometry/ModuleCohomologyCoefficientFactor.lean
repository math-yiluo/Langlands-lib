/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMapFunctorial

/-! # Module coefficient factorization

Source: Stacks Project, Tag 01FB.
(blueprint: new-module-cohomology-coefficient-factor)
-/

@[expose] public section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules

/-- Module coefficient factorization.

Source: Stacks Project, Tag 01FB.
(blueprint: new-module-cohomology-coefficient-factor)

Proof: Apply moduleCohomologyFMap_source_naturality to the coefficient map and the identity of
its direct image. Evaluate the equality of additive maps on x. Composition with the identity
leaves the coefficient map unchanged, and the identity h-map is the edge map. -/
theorem moduleCohomology_coefficient_factor
    {X Y : Scheme.{u}} (f : X ⟶ Y) {N : Y.Modules} {F : X.Modules}
    (φ : N ⟶ (pushforward f).obj F) (p : ℕ)
    (x : (RingedSpace.moduleCohomology Y.toRingedSpace p).obj N) :
    moduleCohomologyFMap (X := X) (Y := Y) (G := N) (F := F) f φ p x =
      moduleCohomologyEdgeMap f F p
        (((RingedSpace.moduleCohomology Y.toRingedSpace p).map φ).hom x) := by
  have he := moduleCohomologyFMap_source_naturality
    (X := X) (Y := Y) (G' := N) (G := (pushforward f).obj F) (F := F)
    f φ (𝟙 ((pushforward f).obj F)) p
  have hx := ConcreteCategory.congr_hom he x
  change moduleCohomologyEdgeMap f F p
      (((RingedSpace.moduleCohomology Y.toRingedSpace p).map φ).hom x) =
    moduleCohomologyFMap (X := X) (Y := Y) (G := N) (F := F)
      f (φ ≫ 𝟙 ((pushforward f).obj F)) p x at hx
  have hid := congrArg (fun ψ : N ⟶ (pushforward f).obj F ↦
    moduleCohomologyFMap (X := X) (Y := Y) (G := N) (F := F) f ψ p x)
    (Category.comp_id φ)
  exact hid.symm.trans hx.symm

end AlgebraicGeometry.Scheme.Modules

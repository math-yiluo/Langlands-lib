/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # The ordinary chart recovery equation

Source: Stacks Project, Tags 0095 and 0096, functoriality of pullback.
(blueprint: def-pc-chart-ordinary-map-recovery).
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The ordinary recovery equation for a map on a pulled-back chart.
Source: Stacks Project, Tags 0095 and 0096.
(blueprint: def-pc-chart-ordinary-map-recovery). -/
@[irreducible] noncomputable def chartOrdinaryMapRecovery
    {X Y Z : Scheme.{u}} (q : Y ⟶ X) (p : Z ⟶ Y) (q₀ : Z ⟶ X)
    (w : p ≫ q = q₀) (U : X.OpenCover.{u}) (a : U.I₀)
    (M N : (U.X a).Modules)
    (ψ : (Scheme.Modules.pullback (U.pullbackHom q₀ a)).obj M ⟶
      (Scheme.Modules.pullback (U.pullbackHom q₀ a)).obj N)
    (s : (Scheme.Modules.pullback (U.pullbackHom q a)).obj M ⟶
      (Scheme.Modules.pullback (U.pullbackHom q a)).obj N) : Prop :=
  let Uk : Y.OpenCover.{u} := U.pullback₁ q
  let V : Z.OpenCover.{u} := Uk.pullback₁ p
  let W : Z.OpenCover.{u} := U.pullback₁ q₀
  let v : V.X a ⟶ W.X a := pullback.lift (V.f a)
    (Uk.pullbackHom p a ≫ U.pullbackHom q a)
    (by
      dsimp only [V]
      rw [Category.assoc, U.pullbackHom_map,
        ← Category.assoc, Uk.pullbackHom_map,
        Category.assoc, w])
  let d := Scheme.Modules.pullbackComp v (U.pullbackHom q₀ a) ≪≫
    Scheme.Modules.pullbackCongr
      (show v ≫ U.pullbackHom q₀ a =
        Uk.pullbackHom p a ≫ U.pullbackHom q a from
          pullback.lift_snd _ _ _) ≪≫
    (Scheme.Modules.pullbackComp (Uk.pullbackHom p a)
      (U.pullbackHom q a)).symm
  d.inv.app M ≫ (Scheme.Modules.pullback v).map ψ ≫ d.hom.app N =
    (Scheme.Modules.pullback (Uk.pullbackHom p a)).map s

end AlgebraicGeometry
